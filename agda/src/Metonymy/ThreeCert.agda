{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Evidence beyond typing, part 3: individuation.
-- A quantified claim "three x (of sort X) with P(c x)" (one coercion) or "three x with P(c x) and Q(d x)"
-- (a copredication, two coercions) is certified by: the routes c (and d), three source referents, for each
-- source referent a referent reached by the route that satisfies the predicate, and for each pair of source
-- referents and each route a referent on which the route's images differ. The distinguishing referents are
-- exactly the evidence for "distinguishable under the coercion", the criterion of individuation.
-- A successful check yields the corresponding Three claim of Metonymy.Quantified in the snapshot's model.
open import Agda.Builtin.Maybe
open import Cubical.Data.Nat using (ℕ)
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.ThreeCert (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; false≢true ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Empty as E
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open Lexicon L
open Routes graph using (Route)
open Checker L
open import Metonymy.Audit graph R using (FinModel ; toModel ; evalR ; evalR⇒ ; ⇒evalR)
open import Metonymy.Semantics graph R using (Model ; interpR)
open import Metonymy.Evidence L R using (KB ; bindM ; nth ; decTrue)
open import Metonymy.Quantified using (Sat ; Indist ; Dist3 ; Three₁ ; Three₂)

private
  decFalse : (b : Bool) → Maybe (b ≡ false)
  decFalse false = just refl
  decFalse true  = nothing

record Triple (X : Type) : Type where
  constructor triple
  field
    first second third : X

-- Evidence for one coercion: its route, predicate, and witnesses.
record RawConj : Type where
  constructor rawConj
  field
    routeN : List ℕ          -- the coercion, as edge names
    predN  : ℕ               -- a predicate, used as a unary relation on the target sort
    sat    : Triple ℕ        -- for each source referent, a target referent it reaches that satisfies the predicate
    dist   : Triple ℕ        -- for the pairs (1,2), (1,3), (2,3): a target referent on which the images differ

record RawThree : Type where
  constructor rawThree
  field
    cname : ℕ                -- a constant whose literal sort is the sort of the quantified variable
    srcs  : Triple ℕ         -- three source referents
    conj1 : RawConj
    conj2 : Maybe RawConj    -- present for a copredication

module Check (K : KB) where
  open KB K

  module Rel {X B : Ty} (r : Route X B) (P : PredId) where
    -- The unary relation a predicate gives on a sort, in the snapshot.
    pr : FinModel.Elem fin B → hProp ℓ-zero
    pr y = (unaryTab P B y ≡ true) , isSetBool _ _

    ρ : FinModel.Elem fin X → FinModel.Elem fin B → hProp ℓ-zero
    ρ = interpR (toModel fin) r

    -- A referent reached by the route that satisfies the predicate.
    checkSat : (x : FinModel.Elem fin X) → ℕ → Maybe (Sat ρ pr x)
    checkSat x j =
      bindM (nth (FinModel.elems fin B) j) (λ y →
      bindM (decTrue (evalR fin r x y)) (λ h1 →
      bindM (decTrue (unaryTab P B y)) (λ h2 →
      just ∣ y , evalR⇒ fin r x y h1 , h2 ∣₁)))

    refute : ∀ x x' w → Indist ρ x x' → evalR fin r x w ≡ true → evalR fin r x' w ≡ false → E.⊥
    refute x x' w h a b =
      false≢true (sym b ∙ ⇒evalR fin r x' w (subst ⟨_⟩ (cong (λ f → f w) h) (evalR⇒ fin r x w a)))

    -- Two source referents are distinguished by a target referent on which the images differ.
    checkDist : (x x' : FinModel.Elem fin X) → ℕ → Maybe (Indist ρ x x' → E.⊥)
    checkDist x x' j = bindM (nth (FinModel.elems fin B) j) (λ w → first w)
      where
        second : ∀ w → Maybe (evalR fin r x' w ≡ true) → Maybe (evalR fin r x w ≡ false) → Maybe (Indist ρ x x' → E.⊥)
        second w (just a) (just b) = just (λ h → refute x' x w (sym h) a b)
        second w _ _ = nothing

        first : ∀ w → Maybe (Indist ρ x x' → E.⊥)
        first w = go w (decTrue (evalR fin r x w)) (decFalse (evalR fin r x' w))
          where
            go : ∀ w → Maybe (evalR fin r x w ≡ true) → Maybe (evalR fin r x' w ≡ false) → Maybe (Indist ρ x x' → E.⊥)
            go w (just a) (just b) = just (λ h → refute x x' w h a b)
            go w _ _ = second w (decTrue (evalR fin r x' w)) (decFalse (evalR fin r x w))

    checkDist3 : (x y z : FinModel.Elem fin X) → Triple ℕ → Maybe (Dist3 ρ x y z)
    checkDist3 x y z (triple j1 j2 j3) =
      bindM (checkDist x y j1) (λ d1 →
      bindM (checkDist x z j2) (λ d2 →
      bindM (checkDist y z j3) (λ d3 → just (d1 , d2 , d3))))

  open Rel using (pr ; ρ)

  -- The result of a successful check.
  data ThreeOK : Type₁ where
    one : ∀ {X B} (r : Route X B) (P : PredId) → Three₁ (ρ r P) (pr r P) → ThreeOK
    two : ∀ {X B C} (r : Route X B) (P : PredId) (s : Route X C) (Q : PredId)
        → Three₂ (ρ r P) (pr r P) (ρ s Q) (pr s Q) → ThreeOK

  -- The data of one coercion, checked against three source referents.
  record ConjOK {X : Ty} (x y z : FinModel.Elem fin X) : Type₁ where
    field
      B : Ty
      r : Route X B
      P : PredId
      satx : Sat (ρ r P) (pr r P) x
      saty : Sat (ρ r P) (pr r P) y
      satz : Sat (ρ r P) (pr r P) z
      dist : Dist3 (ρ r P) x y z

  checkConj : ∀ {X} (x y z : FinModel.Elem fin X) → RawConj → Maybe (ConjOK x y z)
  checkConj {X} x y z (rawConj rn pn (triple s1 s2 s3) d) =
    bindM (predOf pn) (λ P →
    bindM (nth (psig P) 0) (λ B →
    bindM (checkRoute X B rn) (λ r →
    bindM (Rel.checkSat r P x s1) (λ sx →
    bindM (Rel.checkSat r P y s2) (λ sy →
    bindM (Rel.checkSat r P z s3) (λ sz →
    bindM (Rel.checkDist3 r P x y z d) (λ dd →
    just (record { B = B ; r = r ; P = P ; satx = sx ; saty = sy ; satz = sz ; dist = dd }))))))))

  finish : ∀ {X} (x y z : FinModel.Elem fin X) → ConjOK x y z → Maybe RawConj → Maybe ThreeOK
  finish x y z ok1 nothing =
    just (one (ConjOK.r ok1) (ConjOK.P ok1)
              ∣ x , y , z , ConjOK.satx ok1 , ConjOK.saty ok1 , ConjOK.satz ok1 , ConjOK.dist ok1 ∣₁)
  finish x y z ok1 (just c2) =
    bindM (checkConj x y z c2) (λ ok2 →
    just (two (ConjOK.r ok1) (ConjOK.P ok1) (ConjOK.r ok2) (ConjOK.P ok2)
              ∣ x , y , z
              , (ConjOK.satx ok1 , ConjOK.satx ok2)
              , (ConjOK.saty ok1 , ConjOK.saty ok2)
              , (ConjOK.satz ok1 , ConjOK.satz ok2)
              , ConjOK.dist ok1 , ConjOK.dist ok2 ∣₁))

  checkThree : RawThree → Maybe ThreeOK
  checkThree (rawThree cn (triple a1 a2 a3) c1 mc2) =
    bindM (constOf cn) (λ c →
    bindM (nth (FinModel.elems fin (cty c)) a1) (λ x →
    bindM (nth (FinModel.elems fin (cty c)) a2) (λ y →
    bindM (nth (FinModel.elems fin (cty c)) a3) (λ z →
    bindM (checkConj x y z c1) (λ ok1 → finish x y z ok1 mc2)))))
