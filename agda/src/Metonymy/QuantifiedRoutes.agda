{-# OPTIONS --safe --cubical --guardedness #-}

-- Individuation through routes: the count under a route, and under a pair of routes for a copredication,
-- does not depend on which of several equivalent routes the elaboration chose (T6 meets T12).
open import Metonymy.Graph

module Metonymy.QuantifiedRoutes (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R
open import Metonymy.Quantified

module _ (M : Model) (sr : SoundRules M) where
  open Model M

  -- "three P" counted under a route.
  ThreeVia : ∀ {X B} → Route X B → (⟨ Car B ⟩ → hProp ℓ-zero) → Type₁
  ThreeVia r P = Three₁ (interpR M r) P

  -- Equivalent routes give the same count.
  threeVia-indep : ∀ {X B} {r s : Route X B} (P : ⟨ Car B ⟩ → hProp ℓ-zero)
                 → r ≈ s → ThreeVia r P ≡ ThreeVia s P
  threeVia-indep P h = cong (λ ρ → Three₁ ρ P) (sound≈ M sr h)

  -- "three" for a copredication through two routes.
  ThreeVia₂ : ∀ {X B₁ B₂} → Route X B₁ → (⟨ Car B₁ ⟩ → hProp ℓ-zero)
            → Route X B₂ → (⟨ Car B₂ ⟩ → hProp ℓ-zero) → Type₁
  ThreeVia₂ r P s Q = Three₂ (interpR M r) P (interpR M s) Q

  threeVia₂-indep : ∀ {X B₁ B₂} {r r' : Route X B₁} {s s' : Route X B₂} (P : ⟨ Car B₁ ⟩ → hProp ℓ-zero)
                      (Q : ⟨ Car B₂ ⟩ → hProp ℓ-zero)
                  → r ≈ r' → s ≈ s' → ThreeVia₂ r P s Q ≡ ThreeVia₂ r' P s' Q
  threeVia₂-indep P Q h k = cong₂ (λ ρ σ → Three₂ ρ P σ Q) (sound≈ M sr h) (sound≈ M sr k)

  -- The copredication entails the count under each route, whichever representatives were used.
  threeVia₂→₁ : ∀ {X B₁ B₂} (r : Route X B₁) P (s : Route X B₂) Q → ThreeVia₂ r P s Q → ThreeVia r P
  threeVia₂→₁ {X} {B₁} {B₂} r P s Q = Three₂→₁ {X = ⟨ Car X ⟩} {Y₁ = ⟨ Car B₁ ⟩} {Y₂ = ⟨ Car B₂ ⟩} {ρ = interpR M r} {P = P} {σ = interpR M s} {Q = Q}

  threeVia₂→₂ : ∀ {X B₁ B₂} (r : Route X B₁) P (s : Route X B₂) Q → ThreeVia₂ r P s Q → ThreeVia s Q
  threeVia₂→₂ {X} {B₁} {B₂} r P s Q = Three₂→₂ {X = ⟨ Car X ⟩} {Y₁ = ⟨ Car B₁ ⟩} {Y₂ = ⟨ Car B₂ ⟩} {ρ = interpR M r} {P = P} {σ = interpR M s} {Q = Q}
