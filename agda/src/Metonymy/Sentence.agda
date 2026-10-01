{-# OPTIONS --safe --cubical --guardedness #-}

-- Meaning of typed sentences (the output of the certificate checker) in a model, and
-- route independence lifted from routes to whole sentences.
open import Agda.Builtin.List
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Sentence (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Functions.Logic

open Lexicon L
open Routes graph
open Equiv graph R
open Checker L
open import Metonymy.Semantics graph R

-- Tuples of referents for a list of types.
Tuple : Model → List Ty → Type
Tuple M []       = Unit
Tuple M (A ∷ As) = ⟨ Model.Car M A ⟩ × Tuple M As

-- A model of the whole lexicon: referents and edge relations, denotations of constants, predicate relations.
record SModel : Type₁ where
  field
    base    : Model
    ref     : (c : ConstId) → ⟨ Model.Car base (cty c) ⟩
    predRel : (P : PredId) → Tuple base (psig P) → hProp ℓ-zero

module _ (S : SModel) where
  open SModel S

  -- An argument denotes the referents reachable from its constant along its coercion route.
  argsSem : ∀ {As} → Args As → Tuple base As → hProp ℓ-zero
  argsSem anil                     tt       = ⊤
  argsSem (acons (ent c r) as) (y , ys) = interpR base r (ref c) y ⊓ argsSem as ys

  -- Meaning of a sentence: some choice of referents along the routes satisfies the predicate (Retain reading).
  formSem : Form → hProp ℓ-zero
  formSem (pred P as) = ∃[ ys ∶ Tuple base (psig P) ] (argsSem as ys ⊓ predRel P ys)

-- Routes related argument-wise by the declared equivalences.
data _≈A_ : ∀ {As} → Args As → Args As → Type where
  ≈anil  : anil ≈A anil
  ≈acons : ∀ {A As} {c : ConstId} {r r' : Route (cty c) A} {xs ys : Args As}
         → r ≈ r' → xs ≈A ys → acons (ent c r) xs ≈A acons (ent c r') ys

-- T6 for sentences: sentences whose routes differ only by declared equivalences have the same meaning.
module _ (S : SModel) (sr : SoundRules (SModel.base S)) where
  open SModel S

  argsSem-indep : ∀ {As} {xs ys : Args As} → xs ≈A ys → argsSem S xs ≡ argsSem S ys
  argsSem-indep ≈anil = refl
  argsSem-indep {xs = acons (ent c r) xs} {ys = acons (ent .c r') ys} (≈acons h hs) =
    funExt λ { (y , t) →
      cong₂ _⊓_ (cong (λ f → f (ref c) y) (sound≈ base sr h))
                (cong (λ g → g t) (argsSem-indep hs)) }

  formSem-indep : ∀ P {xs ys : Args (psig P)} → xs ≈A ys → formSem S (pred P xs) ≡ formSem S (pred P ys)
  formSem-indep P {xs} {ys} h =
    cong (λ f → ∃[ t ∶ Tuple base (psig P) ] (f t ⊓ predRel P t)) (argsSem-indep h)
