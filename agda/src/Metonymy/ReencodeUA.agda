{-# OPTIONS --safe --cubical --guardedness #-}

-- T15 via univalence. Models re-encoded by equivalences that carry the edge relations along are EQUAL
-- as models (structure identity principle, built by hand with `ua`). Hence every property of models,
-- in particular soundness of the declared equivalences and the truth of any statement defined from a model,
-- transfers along the re-encoding by transport, with no property-specific argument.
open import Metonymy.Graph

module Metonymy.ReencodeUA (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Functions.Logic

open Graph G
open Rules R
open import Metonymy.Semantics G R

-- A model presented as a Sigma type, so that paths between models can be constructed.
ModelΣ : Type₁
ModelΣ = Σ (Ty → Type) (λ Car →
           (∀ A → isSet (Car A))
         × ((e : EdgeId) → Car (src e) → Car (tgt e) → hProp ℓ-zero))

toModel : ModelΣ → Model
toModel (Car , iS , Rel) = record { Car = λ A → Car A , iS A ; EdgeRel = Rel }

module _ (M M' : ModelΣ)
         (e  : ∀ A → fst M A ≃ fst M' A)
         (rc : ∀ ed x y → snd (snd M) ed x y ≡ snd (snd M') ed (equivFun (e (src ed)) x) (equivFun (e (tgt ed)) y))
         where

  private
    carPath : fst M ≡ fst M'
    carPath = funExt λ A → ua (e A)

    setPath : PathP (λ i → ∀ A → isSet (carPath i A)) (fst (snd M)) (fst (snd M'))
    setPath = isProp→PathP (λ i → isPropΠ λ A → isPropIsSet) _ _

    relPath : PathP (λ i → (ed : EdgeId) → carPath i (src ed) → carPath i (tgt ed) → hProp ℓ-zero)
                    (snd (snd M)) (snd (snd M'))
    relPath = funExt λ ed → ua→ λ x → ua→ λ y → rc ed x y

  -- Re-encoded models are equal (univalence).
  model≡ : M ≡ M'
  model≡ = ΣPathP (carPath , ΣPathP (setPath , relPath))

  -- Every property of models is invariant under re-encoding.
  invariance : ∀ {ℓ} (Φ : ModelΣ → Type ℓ) → Φ M ≃ Φ M'
  invariance Φ = pathToEquiv (cong Φ model≡)

  -- In particular, soundness of the declared equivalences.
  soundness-invariant : SoundRules (toModel M) ≃ SoundRules (toModel M')
  soundness-invariant = invariance (λ X → SoundRules (toModel X))
