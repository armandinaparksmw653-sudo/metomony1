{-# OPTIONS --safe --cubical --guardedness #-}

-- T5. Readings form a category: composition of coercion classes is well defined on Coe, associative and
-- unital, and the interpretation is a functor from this category to relations.
open import Metonymy.Graph

module Metonymy.Category (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/ ; elimProp)
import Agda.Builtin.Equality as B

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R

private
  toPath : ∀ {ℓ} {X : Type ℓ} {x y : X} → x B.≡ y → x ≡ y
  toPath B.refl = refl

-- Composition of coercion classes.
infixr 9 _∘C_
_∘C_ : ∀ {A B C} → Coe A B → Coe B C → Coe A C
_∘C_ = SQ.rec2 squash/ (λ r s → [ r ++ s ])
         (λ a b c h → eq/ _ _ (≈-++ˡ c h))
         (λ a b c h → eq/ _ _ (≈-++ʳ a h))

idC : ∀ {A} → Coe A A
idC = [ nil ]

assocC : ∀ {A B C D} (k : Coe A B) (l : Coe B C) (m : Coe C D) → (k ∘C l) ∘C m ≡ k ∘C (l ∘C m)
assocC = SQ.elimProp3 (λ _ _ _ → squash/ _ _) (λ p q r → cong [_] (toPath (++-assoc p q r)))

idLC : ∀ {A B} (k : Coe A B) → idC ∘C k ≡ k
idLC = elimProp (λ _ → squash/ _ _) (λ r → refl)

idRC : ∀ {A B} (k : Coe A B) → k ∘C idC ≡ k
idRC = elimProp (λ _ → squash/ _ _) (λ r → cong [_] (toPath (++-unitʳ r)))

-- The interpretation is a functor: the meaning of a composite is the composite of the meanings.
module _ (M : Model) (sr : SoundRules M) where
  open Model M

  interpC-∘ : ∀ {A B C} (k : Coe A B) (l : Coe B C) → interpC M sr (k ∘C l) ≡ _∘R_ M (interpC M sr k) (interpC M sr l)
  interpC-∘ = SQ.elimProp2 (λ _ _ → isSetΠ2 (λ _ _ → isSetHProp) _ _) (λ r s → interp-++ M r s)

  interpC-id : ∀ {A} → interpC M sr (idC {A}) ≡ interpR M nil
  interpC-id = refl
