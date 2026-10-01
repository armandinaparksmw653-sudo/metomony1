{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Evidence beyond typing, part 1: a knowledge-base snapshot and certificates for the Resolve and Retain
-- modes. A raw certificate now carries, besides the coerced sentence, the referents (indices into the
-- enumerated carriers of the snapshot) that the interpretation selects. The checker recomputes the typed
-- sentence and evaluates the relations in the snapshot; a successful check carries a proof that the chosen
-- referents satisfy the sentence in the snapshot's model.
open import Agda.Builtin.Maybe
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Evidence (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; false≢true ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)
import Cubical.Data.Empty as E
open import Cubical.Functions.Logic
import Agda.Builtin.Equality as B
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)

open Lexicon L
open Routes graph using (Route)
open Checker L
open import Metonymy.Audit graph R using (FinModel ; toModel ; evalR ; evalR⇒ ; ⇒evalR)
import Metonymy.Sentence L R as Sen

------------------------------------------------------------------------------
-- Small utilities

bindM : ∀ {a b} {X : Type a} {Y : Type b} → Maybe X → (X → Maybe Y) → Maybe Y
bindM nothing  f = nothing
bindM (just x) f = f x

nth : ∀ {X : Type} → List X → ℕ → Maybe X
nth []       _       = nothing
nth (x ∷ xs) zero    = just x
nth (x ∷ xs) (suc n) = nth xs n

decTrue : (b : Bool) → Maybe (b ≡ true)
decTrue true  = just refl
decTrue false = nothing

and-true : ∀ x y → x and y ≡ true → (x ≡ true) × (y ≡ true)
and-true true  true  _ = refl , refl
and-true true  false p = E.rec (false≢true p)
and-true false y     p = E.rec (false≢true p)

------------------------------------------------------------------------------
-- A knowledge-base snapshot: a finite model of the lexicon

record KB : Type₁ where
  field
    fin     : FinModel
    refC    : (c : ConstId) → FinModel.Elem fin (cty c)
    predTab : (P : PredId) → Sen.Tuple (toModel fin) (psig P) → Bool
    -- unary use of a predicate on a sort (used for the predicates of quantified sentences)
    unaryTab : (P : PredId) (B : Ty) → FinModel.Elem fin B → Bool

-- The snapshot as a semantic model of sentences.
smodel : KB → Sen.SModel
smodel K = record
  { base    = toModel (KB.fin K)
  ; ref     = KB.refC K
  ; predRel = λ P ys → (KB.predTab K P ys ≡ true) , isSetBool _ _
  }

module _ (K : KB) where
  open KB K

  -- Tuples of referents of a typed sentence.
  FormTuple : Form → Type
  FormTuple (pred P _) = Sen.Tuple (toModel fin) (psig P)

  -- Boolean evaluation of a typed sentence in the snapshot.
  evalArgs : ∀ {As} → Args As → Sen.Tuple (toModel fin) As → Bool
  evalArgs anil                     tt       = true
  evalArgs (acons (ent c r) as) (y , ys) = evalR fin r (refC c) y and evalArgs as ys

  evalForm : (f : Form) → FormTuple f → Bool
  evalForm (pred P as) ys = evalArgs as ys and predTab P ys

  -- What a passed evaluation means semantically: each referent is reached from its constant along the
  -- argument's route, and the predicate holds of the tuple.
  ResolveHolds : (f : Form) → FormTuple f → Type
  ResolveHolds (pred P as) ys = ⟨ Sen.argsSem (smodel K) as ys ⊓ Sen.SModel.predRel (smodel K) P ys ⟩

  evalArgs⇒ : ∀ {As} (as : Args As) (ys : Sen.Tuple (toModel fin) As)
            → evalArgs as ys ≡ true → ⟨ Sen.argsSem (smodel K) as ys ⟩
  evalArgs⇒ anil                     tt       h = tt*
  evalArgs⇒ (acons (ent c r) as) (y , ys) h with and-true _ _ h
  ... | h1 , h2 = evalR⇒ fin r (refC c) y h1 , evalArgs⇒ as ys h2

  evalForm⇒ : ∀ f (ys : FormTuple f) → evalForm f ys ≡ true → ResolveHolds f ys
  evalForm⇒ (pred P as) ys h with and-true _ _ h
  ... | h1 , h2 = evalArgs⇒ as ys h1 , h2

  -- Raw referents (indices into the enumerated carriers) to a tuple of referents.
  resolveTuple : (As : List Ty) → List ℕ → Maybe (Sen.Tuple (toModel fin) As)
  resolveTuple []       []       = just tt
  resolveTuple []       (_ ∷ _)  = nothing
  resolveTuple (_ ∷ _)  []       = nothing
  resolveTuple (A ∷ As) (i ∷ is) =
    bindM (nth (FinModel.elems fin A) i) (λ y →
    bindM (resolveTuple As is) (λ ys → just (y , ys)))

  resolveTupleF : (f : Form) → List ℕ → Maybe (FormTuple f)
  resolveTupleF (pred P _) is = resolveTuple (psig P) is

  ----------------------------------------------------------------------------
  -- Certificates for Resolve and Retain

  record RawResolve : Type where
    constructor rawResolve
    field
      cert : RawCert        -- the coerced sentence, as before
      refs : List ℕ         -- one referent index per argument of the predicate

  -- A passed check: the typed sentence, its referents, and the proof that they satisfy it in the snapshot.
  record Resolved (c : RawCert) : Type₁ where
    field
      form  : Form
      typed : formRaw form B.≡ c
      ys    : FormTuple form
      holds : ResolveHolds form ys

  checkResolve : (raw : RawResolve) → Maybe (Resolved (RawResolve.cert raw))
  checkResolve (rawResolve c is) = go (checkCert c) B.refl
    where
      go : (m : Maybe Form) → checkCert c B.≡ m → Maybe (Resolved c)
      go nothing  _  = nothing
      go (just f) eq =
        bindM (resolveTupleF f is) (λ ys →
        bindM (decTrue (evalForm f ys)) (λ h →
        just (record { form = f ; typed = checkCert-sound c eq ; ys = ys ; holds = evalForm⇒ f ys h })))

  -- Retain: the meaning is the truncated existence of satisfying referents; the witness is only used to prove it.
  retainedF : ∀ f (ys : FormTuple f) → ResolveHolds f ys → ⟨ Sen.formSem (smodel K) f ⟩
  retainedF (pred P as) ys h = ∣ ys , h ∣₁

  retained : ∀ {c} (r : Resolved c) → ⟨ Sen.formSem (smodel K) (Resolved.form r) ⟩
  retained r = retainedF (Resolved.form r) (Resolved.ys r) (Resolved.holds r)
