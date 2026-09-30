{-# OPTIONS --safe --cubical --guardedness #-}
module Everything where

open import Cubical.Foundations.Prelude
open import Cubical.HITs.PropositionalTruncation
open import Cubical.HITs.SetQuotients

-- smoke test: truncation and set quotient are available and typecheck
test : ∀ {ℓ} {A : Type ℓ} → A → ∥ A ∥₁
test = ∣_∣₁
