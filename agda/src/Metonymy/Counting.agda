{-# OPTIONS --safe --cubical --guardedness #-}

-- Individuation: counting is done in the image of the coercion(s) a predicate uses.
--   T12: for a copredication the quantifier demands distinctness under BOTH coercions, and this yields
--        each single-aspect count with no injectivity axiom.
--   T13: a machine-checked countermodel to the schema  "Three Book => Three Info"  (distinct books need
--        not be informationally distinct), which is why the axiom of Chatzikyriakidis-Luo is not derivable.
module Metonymy.Counting where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using (⊥ ; isProp⊥)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁)

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = x ≡ y → ⊥

-- Three elements pairwise distinct AFTER applying the coercion c.
Distinct3 : ∀ {X Y : Type} (c : X → Y) → X → X → X → Type
Distinct3 c x y z = (c x ≢ c y) × (c x ≢ c z) × (c y ≢ c z)

-- "three P", counted in the image of c.
ThreeUnder : ∀ {X Y : Type} (c : X → Y) (P : X → Type) → Type
ThreeUnder {X} c P = ∥ Σ X (λ x → Σ X (λ y → Σ X (λ z → P x × P y × P z × Distinct3 c x y z))) ∥₁

-- "three P" for a predicate that uses two aspects: distinct under both coercions.
ThreeBoth : ∀ {X Y₁ Y₂ : Type} (c₁ : X → Y₁) (c₂ : X → Y₂) (P : X → Type) → Type
ThreeBoth {X} c₁ c₂ P =
  ∥ Σ X (λ x → Σ X (λ y → Σ X (λ z → P x × P y × P z × Distinct3 c₁ x y z × Distinct3 c₂ x y z))) ∥₁

module _ {X Y₁ Y₂ : Type} (c₁ : X → Y₁) (c₂ : X → Y₂) where

  -- T12 (first aspect / second aspect): no injectivity assumption on c₁, c₂.
  ThreeBoth→₁ : ∀ {P} → ThreeBoth c₁ c₂ P → ThreeUnder c₁ P
  ThreeBoth→₁ = PT.rec PT.isPropPropTrunc λ { (x , y , z , px , py , pz , d₁ , d₂) → ∣ x , y , z , px , py , pz , d₁ ∣₁ }

  ThreeBoth→₂ : ∀ {P} → ThreeBoth c₁ c₂ P → ThreeUnder c₂ P
  ThreeBoth→₂ = PT.rec PT.isPropPropTrunc λ { (x , y , z , px , py , pz , d₁ , d₂) → ∣ x , y , z , px , py , pz , d₂ ∣₁ }

  -- "picked up and mastered three books" entails "three physical" and "three informational".
  copredication : ∀ {Q₁ : Y₁ → Type} {Q₂ : Y₂ → Type}
                → ThreeBoth c₁ c₂ (λ x → Q₁ (c₁ x) × Q₂ (c₂ x))
                → ThreeUnder c₁ (λ x → Q₁ (c₁ x)) × ThreeUnder c₂ (λ x → Q₂ (c₂ x))
  copredication {Q₁} {Q₂} h =
    ( PT.rec PT.isPropPropTrunc (λ { (x , y , z , (p₁x , _) , (p₁y , _) , (p₁z , _) , d₁ , _) → ∣ x , y , z , p₁x , p₁y , p₁z , d₁ ∣₁ }) h
    , PT.rec PT.isPropPropTrunc (λ { (x , y , z , (_ , p₂x) , (_ , p₂y) , (_ , p₂z) , _ , d₂) → ∣ x , y , z , p₂x , p₂y , p₂z , d₂ ∣₁ }) h )

------------------------------------------------------------------------------
-- T13. Countermodel: three books (three volumes) but only two works.

data Book : Type where
  b₁ b₂ b₃ : Book

data Work : Type where
  w₁ w₂ : Work

work : Book → Work
work b₁ = w₁
work b₂ = w₁
work b₃ = w₂

private
  isB₁ : Book → Type
  isB₁ b₁ = Unit
  isB₁ b₂ = ⊥
  isB₁ b₃ = ⊥

  isB₂ : Book → Type
  isB₂ b₂ = Unit
  isB₂ b₁ = ⊥
  isB₂ b₃ = ⊥

  b₁≢b₂ : b₁ ≢ b₂
  b₁≢b₂ p = subst isB₁ p tt

  b₁≢b₃ : b₁ ≢ b₃
  b₁≢b₃ p = subst isB₁ p tt

  b₂≢b₃ : b₂ ≢ b₃
  b₂≢b₃ p = subst isB₂ p tt

  -- pigeonhole on two works: no three pairwise distinct works
  pigeon : (a b c : Work) → a ≢ b → a ≢ c → b ≢ c → ⊥
  pigeon w₁ w₁ c ab ac bc = ab refl
  pigeon w₁ w₂ w₁ ab ac bc = ac refl
  pigeon w₁ w₂ w₂ ab ac bc = bc refl
  pigeon w₂ w₁ w₁ ab ac bc = bc refl
  pigeon w₂ w₁ w₂ ab ac bc = ac refl
  pigeon w₂ w₂ c ab ac bc = ab refl

-- Three books, distinct as books (identity coercion) ...
threeBooks : ThreeUnder (λ (b : Book) → b) (λ _ → Unit)
threeBooks = ∣ b₁ , b₂ , b₃ , tt , tt , tt , b₁≢b₂ , b₁≢b₃ , b₂≢b₃ ∣₁

-- ... but not three informationally distinct ones.
not-threeWorks : ThreeUnder work (λ _ → Unit) → ⊥
not-threeWorks = PT.rec isProp⊥ λ { (x , y , z , _ , _ , _ , dxy , dxz , dyz) → pigeon (work x) (work y) (work z) dxy dxz dyz }

-- T13: "Three Book => Three Info" is not valid without an injectivity axiom.
CL15-schema-fails : (ThreeUnder (λ (b : Book) → b) (λ _ → Unit)) × (ThreeUnder work (λ _ → Unit) → ⊥)
CL15-schema-fails = threeBooks , not-threeWorks
