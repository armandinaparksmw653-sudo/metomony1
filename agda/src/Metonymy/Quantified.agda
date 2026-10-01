{-# OPTIONS --safe --cubical --guardedness #-}

-- T12 (full form). Individuation for relational coercions.
-- A referent is distinguished from another under a coercion when the coercion relates them to different
-- things. "three P" demands pairwise distinguishability under every coercion the predicates use, so a
-- copredication entails each single-aspect count, no injectivity axiom is needed, the criterion does not
-- depend on which equivalent route was used, and for functional coercions it is the usual kernel criterion.
module Metonymy.Quantified where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
import Cubical.Data.Empty as E
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open import Metonymy.Counting using (ThreeUnder ; Distinct3)

module _ {X Y : Type} where

  -- Some referent reachable by the coercion satisfies the predicate.
  Sat : (X → Y → hProp ℓ-zero) → (Y → hProp ℓ-zero) → X → Type
  Sat ρ P x = ⟨ ∃[ y ∶ Y ] (ρ x y ⊓ P y) ⟩

  -- Two referents are indistinguishable under a coercion when it relates them to the same things.
  Indist : (X → Y → hProp ℓ-zero) → X → X → Type₁
  Indist ρ x x' = ρ x ≡ ρ x'

  Dist3 : (X → Y → hProp ℓ-zero) → X → X → X → Type₁
  Dist3 ρ x y z = (Indist ρ x y → E.⊥) × (Indist ρ x z → E.⊥) × (Indist ρ y z → E.⊥)

  -- "three P" counted under a coercion.
  Three₁ : (X → Y → hProp ℓ-zero) → (Y → hProp ℓ-zero) → Type₁
  Three₁ ρ P = ∥ Σ X (λ x → Σ X (λ y → Σ X (λ z →
                 Sat ρ P x × Sat ρ P y × Sat ρ P z × Dist3 ρ x y z))) ∥₁

module _ {X Y₁ Y₂ : Type} where

  -- "three" for a conjunction of two predicates, each through its own coercion:
  -- distinguishable under both coercions.
  Three₂ : (X → Y₁ → hProp ℓ-zero) → (Y₁ → hProp ℓ-zero)
         → (X → Y₂ → hProp ℓ-zero) → (Y₂ → hProp ℓ-zero) → Type₁
  Three₂ ρ P σ Q = ∥ Σ X (λ x → Σ X (λ y → Σ X (λ z →
                     (Sat ρ P x × Sat σ Q x) × (Sat ρ P y × Sat σ Q y) × (Sat ρ P z × Sat σ Q z)
                   × Dist3 ρ x y z × Dist3 σ x y z))) ∥₁

  -- Entailment to each single-aspect count. No injectivity of the coercions is assumed.
  Three₂→₁ : ∀ {ρ P σ Q} → Three₂ ρ P σ Q → Three₁ ρ P
  Three₂→₁ = PT.rec isPropPropTrunc λ { (x , y , z , (a , _) , (b , _) , (c , _) , d₁ , d₂) →
    ∣ x , y , z , a , b , c , d₁ ∣₁ }

  Three₂→₂ : ∀ {ρ P σ Q} → Three₂ ρ P σ Q → Three₁ σ Q
  Three₂→₂ = PT.rec isPropPropTrunc λ { (x , y , z , (_ , a) , (_ , b) , (_ , c) , d₁ , d₂) →
    ∣ x , y , z , a , b , c , d₂ ∣₁ }

------------------------------------------------------------------------------
-- Functional coercions: the relational criterion is the kernel criterion

module Functional {X Y : Type} (isSetY : isSet Y) (f : X → Y) where

  graphRel : X → Y → hProp ℓ-zero
  graphRel x y = (y ≡ f x) , isSetY y (f x)

  -- Indistinguishable under the graph of f exactly when f agrees.
  indist⇒ : ∀ x x' → Indist graphRel x x' → f x ≡ f x'
  indist⇒ x x' h = subst ⟨_⟩ (cong (λ g → g (f x)) h) refl

  ⇒indist : ∀ x x' → f x ≡ f x' → Indist graphRel x x'
  ⇒indist x x' p = cong (λ t y → (y ≡ t) , isSetY y t) p

  -- Satisfaction through the graph of f is satisfaction of the predicate at f x.
  sat⇒ : ∀ (P : Y → hProp ℓ-zero) x → Sat graphRel P x → ⟨ P (f x) ⟩
  sat⇒ P x = PT.rec (isProp⟨⟩ (P (f x))) λ { (y , p , q) → subst (λ t → ⟨ P t ⟩) p q }

  ⇒sat : ∀ (P : Y → hProp ℓ-zero) x → ⟨ P (f x) ⟩ → Sat graphRel P x
  ⇒sat P x q = ∣ f x , refl , q ∣₁

  dist⇒ : ∀ {x y z} → Dist3 graphRel x y z → Distinct3 f x y z
  dist⇒ (a , b , c) = (λ p → a (⇒indist _ _ p)) , (λ p → b (⇒indist _ _ p)) , (λ p → c (⇒indist _ _ p))

  ⇒dist : ∀ {x y z} → Distinct3 f x y z → Dist3 graphRel x y z
  ⇒dist (a , b , c) = (λ h → a (indist⇒ _ _ h)) , (λ h → b (indist⇒ _ _ h)) , (λ h → c (indist⇒ _ _ h))

  -- For a functional coercion the relational count is the count in the image (T12 meets T14).
  three⇒ : ∀ (Q : Y → hProp ℓ-zero) → Three₁ graphRel Q → ThreeUnder f (λ x → ⟨ Q (f x) ⟩)
  three⇒ Q = PT.rec isPropPropTrunc λ { (x , y , z , a , b , c , d) →
    ∣ x , y , z , sat⇒ Q x a , sat⇒ Q y b , sat⇒ Q z c , dist⇒ d ∣₁ }

  ⇒three : ∀ (Q : Y → hProp ℓ-zero) → ThreeUnder f (λ x → ⟨ Q (f x) ⟩) → Three₁ graphRel Q
  ⇒three Q = PT.rec isPropPropTrunc λ { (x , y , z , a , b , c , d) →
    ∣ x , y , z , ⇒sat Q x a , ⇒sat Q y b , ⇒sat Q z c , ⇒dist d ∣₁ }
