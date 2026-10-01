{-# OPTIONS --safe --cubical --guardedness #-}

-- C1, the central correspondence: coherence of coercions is the statement that the type of readings
-- Coe A B is a proposition, and the uniqueness of the coercion is that it is contractible.
--   * [r] = [s] in Coe  iff  r and s are (mere) equivalent routes (effectiveness of the quotient);
--   * Coe A B is a proposition  iff  any two routes are equivalent (coherence in the sense of Luo);
--   * Coe A B is contractible  iff  a route exists and coherence holds.
-- Equivalence of routes is a relation with proof-relevant derivations, so "equivalent" is truncated.
open import Metonymy.Graph

module Metonymy.Coherence (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; squash/ ; elimProp ; elimProp2)
open import Cubical.HITs.SetQuotients.Properties using (isEquivRel→TruncIso)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open Graph G
open Routes G
open Equiv G R
open import Metonymy.Semantics G R using (Coe)

≈-isEquivRel : ∀ {A B} → BinaryRelation.isEquivRel (_≈_ {A} {B})
≈-isEquivRel = BinaryRelation.equivRel (λ _ → ≈-refl) (λ _ _ → ≈-sym) (λ _ _ _ → ≈-trans)

-- Two routes name the same reading exactly when they are merely equivalent.
readings-equal : ∀ {A B} (r s : Route A B) → Iso (Path (Coe A B) [ r ] [ s ]) ∥ r ≈ s ∥₁
readings-equal r s = isEquivRel→TruncIso ≈-isEquivRel r s

-- Coherence, stated for a pair of types: any two routes are equivalent.
Coherent₂ : Ty → Ty → Type
Coherent₂ A B = ∀ (r s : Route A B) → ∥ r ≈ s ∥₁

-- Coherence is exactly "the set of readings is a proposition".
coherent⇒isProp : ∀ {A B} → Coherent₂ A B → isProp (Coe A B)
coherent⇒isProp coh = elimProp2 (λ _ _ → squash/ _ _) (λ r s → Iso.inv (readings-equal r s) (coh r s))

isProp⇒coherent : ∀ {A B} → isProp (Coe A B) → Coherent₂ A B
isProp⇒coherent p r s = Iso.fun (readings-equal r s) (p [ r ] [ s ])

-- Uniqueness of the coercion: a route exists and coherence holds, exactly when Coe is contractible.
contractible⇒exists×coherent : ∀ {A B} → isContr (Coe A B) → ∥ Route A B ∥₁ × Coherent₂ A B
contractible⇒exists×coherent {A} {B} (c , uniq) =
  elimProp {P = λ _ → ∥ Route A B ∥₁} (λ _ → isPropPropTrunc) (λ r → ∣ r ∣₁) c
  , isProp⇒coherent (isContr→isProp (c , uniq))

exists×coherent⇒contractible : ∀ {A B} → ∥ Route A B ∥₁ × Coherent₂ A B → isContr (Coe A B)
exists×coherent⇒contractible {A} {B} (ex , coh) =
  PT.rec isPropIsContr (λ r → inhProp→isContr [ r ] (coherent⇒isProp coh)) ex
