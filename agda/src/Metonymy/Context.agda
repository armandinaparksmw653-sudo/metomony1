{-# OPTIONS --safe --cubical --guardedness #-}

-- Context as enabling of coercions (corrected T8).
-- Words of the context switch coercion edges on or off. Semantically a disabled edge relates nothing.
--   * a route made only of enabled edges means the same in the restricted and the full model;
--   * a route through a disabled edge means nothing in the restricted model;
--   * if the declared equivalences respect enabledness, soundness of the rules survives restriction,
--     so the readings available in a context are well defined classes of Coe.
open import Metonymy.Graph

module Metonymy.Context (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; if_then_else_ ; false≢true ; isSetBool)
import Cubical.Data.Empty as E
open import Cubical.Functions.Logic
open import Cubical.HITs.SetQuotients as SQ using ([_])
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁)

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R

private
  and-assoc : ∀ x y z → x and (y and z) ≡ (x and y) and z
  and-assoc false y z = refl
  and-assoc true  y z = refl

  and-true : ∀ x y → x and y ≡ true → (x ≡ true) × (y ≡ true)
  and-true true  true  _ = refl , refl
  and-true true  false p = E.rec (false≢true p)
  and-true false y     p = E.rec (false≢true p)

-- Truncated existence over a body made of two parts (the shape used by interpR for a non-empty route).
ex : ∀ {X : Type} → (X → hProp ℓ-zero) → (X → hProp ℓ-zero) → hProp ℓ-zero
ex rel rest = ∃[ y ∶ _ ] (rel y ⊓ rest y)

-- A gate keeps a proposition when the flag is on and replaces it by falsity otherwise.
gate : Bool → hProp ℓ-zero → hProp ℓ-zero
gate b P = if b then P else ⊥

gate-true : ∀ b (P : hProp ℓ-zero) → b ≡ true → gate b P ≡ P
gate-true true  P _ = refl
gate-true false P p = E.rec (false≢true p)

module _ (en : EdgeId → Bool) where

  -- A route is enabled when all of its edges are.
  Enabled : ∀ {A B} → Route A B → Bool
  Enabled nil        = true
  Enabled (cons e r) = en e and Enabled r

  Enabled-++ : ∀ {A B C} (p : Route A B) (q : Route B C) → Enabled (p ++ q) ≡ Enabled p and Enabled q
  Enabled-++ nil        q = refl
  Enabled-++ (cons e p) q = cong (λ t → en e and t) (Enabled-++ p q) ∙ and-assoc (en e) (Enabled p) (Enabled q)

  -- The declared equivalences respect enabledness.
  RespectEn : Type
  RespectEn = ∀ ρ → Enabled (lhs ρ) ≡ Enabled (rhs ρ)

  Enabled-resp : RespectEn → ∀ {A B} {r s : Route A B} → r ≈ s → Enabled r ≡ Enabled s
  Enabled-resp rs ≈-refl        = refl
  Enabled-resp rs (≈-sym h)     = sym (Enabled-resp rs h)
  Enabled-resp rs (≈-trans h k) = Enabled-resp rs h ∙ Enabled-resp rs k
  Enabled-resp rs (≈-step ρ p s) =
      Enabled-++ p (lhs ρ ++ s)
    ∙ cong (λ t → Enabled p and t)
        (Enabled-++ (lhs ρ) s ∙ cong (λ t → t and Enabled s) (rs ρ) ∙ sym (Enabled-++ (rhs ρ) s))
    ∙ sym (Enabled-++ p (rhs ρ ++ s))

  -- Enabledness is a property of a reading class.
  EnabledC : RespectEn → ∀ {A B} → Coe A B → Bool
  EnabledC rs = SQ.rec isSetBool Enabled (λ r s h → Enabled-resp rs h)

  -- The model seen through the context: disabled edges relate nothing.
  restrict : Model → Model
  restrict M = record
    { Car     = Model.Car M
    ; EdgeRel = λ e x y → gate (en e) (Model.EdgeRel M e x y)
    }

  module _ (M : Model) where
    open Model M

    -- Enabled routes mean the same in the restricted model.
    restrict-enabled : ∀ {A B} (r : Route A B) → Enabled r ≡ true → interpR (restrict M) r ≡ interpR M r
    restrict-enabled nil _ = refl
    restrict-enabled (cons e r) d =
      funExt λ x → funExt λ z →
        cong₂ ex (funExt λ y → gate-true (en e) (EdgeRel e x y) (fst (and-true (en e) (Enabled r) d)))
                 (funExt λ y → cong (λ f → f y z) (restrict-enabled r (snd (and-true (en e) (Enabled r) d))))

    private
      cons-disabled : ∀ (b c : Bool) (P Q : hProp ℓ-zero)
                    → b and c ≡ false → ⟨ gate b P ⟩ → ⟨ Q ⟩ → (c ≡ false → ⟨ Q ⟩ → E.⊥) → E.⊥
      cons-disabled false c P Q _ h1 h2 ih = h1
      cons-disabled true  c P Q d h1 h2 ih = ih d h2

    -- Routes through a disabled edge mean nothing in the restricted model.
    restrict-disabled : ∀ {A B} (r : Route A B) → Enabled r ≡ false
                      → ∀ x y → ⟨ interpR (restrict M) r x y ⟩ → E.⊥
    restrict-disabled nil d x y h = E.rec (false≢true (sym d))
    restrict-disabled (cons e r) d x z =
      PT.rec E.isProp⊥ (λ { (y , h1 , h2) →
        cons-disabled (en e) (Enabled r) (EdgeRel e x y) (interpR (restrict M) r y z) d h1 h2
          (λ dr h → restrict-disabled r dr y z h) })

    -- Soundness of the declared equivalences survives restriction.
    restrict-sound : RespectEn → SoundRules M → SoundRules (restrict M)
    restrict-sound rs sr ρ = by-cases (Enabled (lhs ρ)) refl
      where
        by-cases : (b : Bool) → Enabled (lhs ρ) ≡ b → interpR (restrict M) (lhs ρ) ≡ interpR (restrict M) (rhs ρ)
        by-cases true eqL =
          restrict-enabled (lhs ρ) eqL ∙ sr ρ ∙ sym (restrict-enabled (rhs ρ) (sym (rs ρ) ∙ eqL))
        by-cases false eqL =
          funExt λ x → funExt λ y →
            ⇔toPath (λ h → E.rec (restrict-disabled (lhs ρ) eqL x y h))
                    (λ h → E.rec (restrict-disabled (rhs ρ) (sym (rs ρ) ∙ eqL) x y h))
