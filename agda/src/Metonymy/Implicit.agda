{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- T4, first-order fragment. Implicit coercive typing in the style of Luo: a constant fits a slot when
-- SOME coercion route exists. We prove, for predicate sentences with constant arguments:
--   (soundness)    every explicit elaboration is implicitly well typed;
--   (completeness) every implicitly well typed sentence has an explicit elaboration;
--   (uniqueness)   under coherence of the coercions, any two elaborations agree up to the equivalence.
-- This covers the first-order fragment only; the full metatheory of coercive subtyping (dependent types,
-- conservativity over the logical framework) is not formalized.
open import Agda.Builtin.List
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Implicit (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open Lexicon L
open Routes graph
open Equiv graph R
open Checker L
open import Metonymy.Sentence L R using (_≈A_ ; ≈anil ; ≈acons)

-- The surface of an argument list: constants only, no coercions.
data CArgs : List Ty → Type where
  cnil  : CArgs []
  ccons : ∀ {A As} → ConstId → CArgs As → CArgs (A ∷ As)

strip : ∀ {As} → Args As → CArgs As
strip anil                 = cnil
strip (acons (ent c _) as) = ccons c (strip as)

-- Implicit typing: each constant has some coercion route to its slot.
Fits : ∀ {As} → CArgs As → Type
Fits cnil                = Unit
Fits (ccons {A} c cs)    = ∥ Route (cty c) A ∥₁ × Fits cs

-- Soundness: an explicit elaboration witnesses implicit typing.
elab-sound : ∀ {As} (as : Args As) → Fits (strip as)
elab-sound anil                 = tt
elab-sound (acons (ent c r) as) = ∣ r ∣₁ , elab-sound as

-- Completeness: implicit typing yields an explicit elaboration with the given surface.
elab-complete : ∀ {As} (cs : CArgs As) → Fits cs → ∥ Σ (Args As) (λ as → strip as ≡ cs) ∥₁
elab-complete cnil        _          = ∣ anil , refl ∣₁
elab-complete (ccons c cs) (pr , fs) =
  PT.rec isPropPropTrunc (λ r →
    PT.rec isPropPropTrunc (λ { (as , eq) → ∣ acons (ent c r) as , cong (ccons c) eq ∣₁ }) (elab-complete cs fs)) pr

-- Coherence: all coercions between two types are equivalent.
Coherent : Type
Coherent = ∀ {A B} (r s : Route A B) → r ≈ s

private
  headC : ∀ {A As} → CArgs (A ∷ As) → ConstId
  headC (ccons c _) = c

  tailC : ∀ {A As} → CArgs (A ∷ As) → CArgs As
  tailC (ccons _ cs) = cs

-- Uniqueness: under coherence, two elaborations of the same surface differ only by the equivalence.
elab-unique : Coherent → ∀ {As} (as bs : Args As) → strip as ≡ strip bs → as ≈A bs
elab-unique coh anil anil _ = ≈anil
elab-unique coh (acons (ent c r) xs) (acons (ent c' r') ys) eq =
  J (λ d _ → (r'' : Route (cty d) _) → acons (ent c r) xs ≈A acons (ent d r'') ys)
    (λ r'' → ≈acons (coh r r'') (elab-unique coh xs ys (cong tailC eq)))
    (cong headC eq) r'
