{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Evidence beyond typing, part 2: a family of readings.
-- A certificate lists candidate routes for one coerced argument, pairs of readings claimed to be different
-- (each with a pair of referents on which one route relates and the other does not), and pairs claimed to
-- be the same reading (each with chains of rewriting steps to a common route). The checker validates every
-- route, every apartness witness in the snapshot, and every chain; what it returns is a list of proved
-- claims about the set of readings Coe: some pairs are distinct points, some are equal.
open import Agda.Builtin.Maybe
open import Cubical.Data.Nat using (ℕ)
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.FamilyCert
  (L : Lexicon) (R : Rules (Lexicon.graph L))
  (ruleOf : ℕ → Maybe (Rules.RuleId R))
  where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ)
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (discreteList)
import Cubical.Data.Empty as E
open import Cubical.Relation.Nullary using (Dec ; yes ; no)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/)
import Agda.Builtin.Equality as B

open Lexicon L
open Routes graph using (Route ; nil ; cons) renaming (_++_ to _++ʳ_)
open Rules R
open Equiv graph R
open Checker L
import Metonymy.Enumerate L as En
import Metonymy.TypedFactor L as TF
import Metonymy.NormalizeFull L R as NF
open NF using (lhsN ; rhsN ; module S)
open import Metonymy.Audit graph R using (FinModel ; toModel ; evalR ; evalR⇒ ; ⇒evalR)
open import Metonymy.Semantics graph R using (Model ; SoundRules ; Coe ; interpR)
open import Metonymy.Equivalence graph R using (Apart ; apart⇒distinct)
open import Metonymy.Evidence L R using (KB ; bindM ; nth ; decTrue)

private
  toPath : ∀ {ℓ} {X : Type ℓ} {x y : X} → x B.≡ y → x ≡ y
  toPath B.refl = refl

  mapM : ∀ {a b} {X : Type a} {Y : Type b} → (X → Maybe Y) → List X → Maybe (List Y)
  mapM f []       = just []
  mapM f (x ∷ xs) = bindM (f x) (λ y → bindM (mapM f xs) (λ ys → just (y ∷ ys)))

  decFalse : (b : Bool) → Maybe (b ≡ false)
  decFalse false = just refl
  decFalse true  = nothing

------------------------------------------------------------------------------
-- Raw evidence

record RawStep : Type where
  constructor rawStep
  field
    ruleN : ℕ
    pre   : List ℕ
    post  : List ℕ

record RawApart : Type where
  constructor rawApart
  field
    left right : ℕ      -- indices into the list of readings
    srcRef     : ℕ      -- referent index in the source carrier
    tgtRef     : ℕ      -- referent index in the target carrier

record RawSame : Type where
  constructor rawSame
  field
    left right : ℕ                  -- indices into the list of readings
    leftSteps rightSteps : List RawStep

record RawFamily : Type where
  constructor rawFamily
  field
    cname    : ℕ                 -- the constant being coerced
    pname    : ℕ                 -- the predicate whose slot it fills
    slot     : ℕ                 -- which argument slot
    readings : List (List ℕ)     -- candidate routes, as lists of edge names
    apart    : List RawApart
    same     : List RawSame

-- Proved claims about the set of readings between two types.
data Claim (A B : Ty) : Type₁ where
  distinct : (r s : Route A B) → (Path (Coe A B) [ r ] [ s ] → E.⊥) → Claim A B
  equal    : (r s : Route A B) → Path (Coe A B) [ r ] [ s ] → Claim A B

record FamilyOK : Type₁ where
  field
    A B      : Ty
    readings : List (Route A B)
    claims   : List (Claim A B)

------------------------------------------------------------------------------
-- Checking

-- Left-hand sides of rules have at least one edge (needed to lift rewriting steps to typed routes).
module _ (ne : ∀ ρ → lhsN ρ ≡ [] → E.⊥) where
  open NF.LiftSteps ne

  -- Apply one raw step to a list of names, producing a step of the string rewriting relation.
  applyStep : RawStep → (u : List ℕ) → Maybe (Σ (List ℕ) (λ v → u S.⇒s v))
  applyStep (rawStep n pre post) u = bindM (ruleOf n) (λ ρ → go ρ (discreteList discreteℕ u (pre ++ (lhsN ρ ++ post))))
    where
      go : ∀ ρ → Dec (u ≡ pre ++ (lhsN ρ ++ post)) → Maybe (Σ (List ℕ) (λ v → u S.⇒s v))
      go ρ (yes e) = just (pre ++ (rhsN ρ ++ post) , ρ , pre , post , e , refl)
      go ρ (no _)  = nothing

  applySteps : List RawStep → (u : List ℕ) → Maybe (Σ (List ℕ) (λ v → u S.→* v))
  applySteps []         u = just (u , S.ε)
  applySteps (st ∷ sts) u =
    bindM (applyStep st u) (λ { (v , step) →
    bindM (applySteps sts v) (λ { (w , ch) → just (w , step S.▹ ch) }) })

  -- Two routes related by chains of rewriting steps reaching the same names are equivalent.
  checkSame : ∀ {A B} (ls rs : List RawStep) (r s : Route A B) → Maybe (r ≈ s)
  checkSame ls rs r s =
    bindM (applySteps ls (routeNames r)) (λ { (m1 , c1) →
    bindM (applySteps rs (routeNames s)) (λ { (m2 , c2) →
    go m1 c1 m2 c2 (discreteList discreteℕ m1 m2) }) })
    where
      go : ∀ m1 → routeNames r S.→* m1 → ∀ m2 → routeNames s S.→* m2 → Dec (m1 ≡ m2) → Maybe (r ≈ s)
      go m1 c1 m2 c2 (no _)  = nothing
      go m1 c1 m2 c2 (yes e) with lift-chain r refl c1 | lift-chain s refl c2
      ... | r1 , nr1 , r≈r1 | s1 , ns1 , s≈s1 =
        let r1≡s1 : r1 ≡ s1
            r1≡s1 = En.routeNames-inj (nr1 ∙ e ∙ sym ns1)
        in just (≈-trans (subst (λ x → r ≈ x) r1≡s1 r≈r1) (≈-sym s≈s1))

module Check (K : KB) (sr : SoundRules (toModel (KB.fin K))) (ne : ∀ ρ → lhsN ρ ≡ [] → E.⊥) where
  open KB K

  -- An apartness witness: referents x, y with r relating them and s not.
  checkApart : ∀ {A B} (r s : Route A B) (i j : ℕ) → Maybe (Path (Coe A B) [ r ] [ s ] → E.⊥)
  checkApart {A} {B} r s i j =
    bindM (nth (FinModel.elems fin A) i) (λ x →
    bindM (nth (FinModel.elems fin B) j) (λ y →
    bindM (decTrue (evalR fin r x y)) (λ h1 →
    bindM (decFalse (evalR fin s x y)) (λ h2 →
    just (apart⇒distinct (toModel fin) sr
            (x , y , evalR⇒ fin r x y h1
                   , (λ hs → false≢true (sym h2 ∙ ⇒evalR fin s x y hs))))))))

  claimApart : ∀ {A B} → List (Route A B) → RawApart → Maybe (Claim A B)
  claimApart rs (rawApart i j x y) =
    bindM (nth rs i) (λ r → bindM (nth rs j) (λ s →
    bindM (checkApart r s x y) (λ d → just (distinct r s d))))

  claimSame : ∀ {A B} → List (Route A B) → RawSame → Maybe (Claim A B)
  claimSame rs (rawSame i j ls rts) =
    bindM (nth rs i) (λ r → bindM (nth rs j) (λ s →
    bindM (checkSame ne ls rts r s) (λ h → just (equal r s (eq/ r s h)))))

  -- Check a whole family of readings.
  checkFamily : RawFamily → Maybe FamilyOK
  checkFamily (rawFamily cn pn slot readings apart same) =
    bindM (constOf cn) (λ c →
    bindM (predOf pn) (λ P →
    bindM (nth (psig P) slot) (λ B →
    bindM (mapM (checkRoute (cty c) B) readings) (λ rs →
    bindM (mapM (claimApart rs) apart) (λ as →
    bindM (mapM (claimSame rs) same) (λ ss →
    just (record { A = cty c ; B = B ; readings = rs ; claims = as ++ ss })))))))
