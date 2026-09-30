{-# OPTIONS --safe --cubical-compatible #-}

-- Minimal prelude for the syntactic layer (Agda builtins only, so this layer stays compilable).
module Metonymy.Base where

open import Agda.Builtin.Equality public
open import Agda.Builtin.List     public
open import Agda.Builtin.Maybe    public
open import Agda.Builtin.Nat      public renaming (Nat to ℕ)
open import Agda.Builtin.Sigma    public
open import Agda.Builtin.Unit     public

infixr 2 _×_
_×_ : Set → Set → Set
A × B = Σ A (λ _ → B)

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

data Dec (A : Set) : Set where
  yes : A → Dec A
  no  : ¬ A → Dec A

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : ∀ {A B C : Set} (f : A → B → C) {x x' : A} {y y' : B} → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
cong₂ f refl refl = refl

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

mapMaybe : ∀ {A B : Set} → (A → B) → Maybe A → Maybe B
mapMaybe f nothing  = nothing
mapMaybe f (just x) = just (f x)

unJust : ∀ {A : Set} → A → Maybe A → A
unJust d nothing  = d
unJust d (just x) = x

just-inj : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj {x = x} p = cong (unJust x) p

-- If a mapped Maybe is `just`, the source was `just`.
mapMaybe-just : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y : B}
              → mapMaybe f m ≡ just y → Σ A (λ x → (m ≡ just x) × (f x ≡ y))
mapMaybe-just f nothing  ()
mapMaybe-just f (just x) eq = x , refl , just-inj eq
