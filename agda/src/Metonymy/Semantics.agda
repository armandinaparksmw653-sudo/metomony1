{-# OPTIONS --safe --cubical --guardedness #-}

-- Semantic layer: models, relational interpretation of routes, the quotient Coe of routes by the
-- declared two-cells, Route independence (T6) and the Retain/Resolve modes.
open import Metonymy.Graph

module Metonymy.Semantics (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.Logic
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; squash/)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; isPropPropTrunc)

open Graph G
open Routes G
open Rules R
open Equiv G R

-- A model: a set of referents for each sense type and a proposition-valued relation for each edge.
record Model : Type₁ where
  field
    Car     : Ty → hSet ℓ-zero
    EdgeRel : (e : EdgeId) → ⟨ Car (src e) ⟩ → ⟨ Car (tgt e) ⟩ → hProp ℓ-zero

-- Coercions between A and B: routes modulo the declared equivalences. A set by construction.
Coe : Ty → Ty → Type
Coe A B = Route A B / _≈_

isSetCoe : ∀ {A B} → isSet (Coe A B)
isSetCoe = squash/

module _ (M : Model) where
  open Model M

  -- Relational interpretation of a route (one-to-many: a coercion need not be a function).
  interpR : ∀ {A B} → Route A B → ⟨ Car A ⟩ → ⟨ Car B ⟩ → hProp ℓ-zero
  interpR {A} nil x y = (x ≡ y) , str (Car A) x y
  interpR (cons e r) x z = ∃[ y ∶ ⟨ Car (tgt e) ⟩ ] (EdgeRel e x y ⊓ interpR r y z)

  -- Every declared two-cell is semantically valid in M.
  SoundRules : Type₁
  SoundRules = ∀ (ρ : RuleId) → interpR (lhs ρ) ≡ interpR (rhs ρ)

  ---------------------------------------------------------------------------
  -- Route independence (T6): statement; proof below (sound≈, routeIndependence)

  -- T6. Route independence: equivalent routes have the same meaning.
  RouteIndependence : Type₁
  RouteIndependence = SoundRules → ∀ {A B} {r s : Route A B} → r ≈ s → interpR r ≡ interpR s

  ---------------------------------------------------------------------------
  -- Interpretation modes for a fixed route r, predicate P on the target, source referent x

  -- Retain: the meaning is that some referent reachable by r satisfies P (truncated existence).
  Retain : ∀ {A B} → Route A B → (⟨ Car B ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  Retain r P x = ∃[ y ∶ _ ] (interpR r x y ⊓ P y)

  -- Resolve: a particular referent y has been selected.
  Resolve : ∀ {A B} → Route A B → ⟨ Car B ⟩ → (⟨ Car B ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  Resolve r y P x = interpR r x y ⊓ P y

  -- T9' (part). Resolve entails Retain.
  Resolve⇒Retain : ∀ {A B} (r : Route A B) (y : ⟨ Car B ⟩) (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩)
                 → ⟨ Resolve r y P x ⟩ → ⟨ Retain r P x ⟩
  Resolve⇒Retain r y P x h = ∣ y , h ∣₁

  ---------------------------------------------------------------------------
  -- F2: composition of relations and proofs of T6, T9' (part)

  -- Composition of (proposition-valued) relations, generic in the carriers.
  _∘R_ : ∀ {X Y Z : Type} → (X → Y → hProp ℓ-zero) → (Y → Z → hProp ℓ-zero) → X → Z → hProp ℓ-zero
  (S ∘R T) x z = ∃[ y ∶ _ ] (S x y ⊓ T y z)

  ++→ : ∀ {A B C} (p : Route A B) (q : Route B C) (x : ⟨ Car A ⟩) (z : ⟨ Car C ⟩)
      → ⟨ interpR (p ++ q) x z ⟩ → ⟨ (interpR p ∘R interpR q) x z ⟩
  ++→ nil        q x z h = ∣ x , refl , h ∣₁
  ++→ (cons e p) q x z = PT.rec isPropPropTrunc λ
    { (y , Exy , h) → PT.rec isPropPropTrunc (λ { (w , hp , hq) → ∣ w , ∣ y , Exy , hp ∣₁ , hq ∣₁ }) (++→ p q y z h) }

  ++← : ∀ {A B C} (p : Route A B) (q : Route B C) (x : ⟨ Car A ⟩) (z : ⟨ Car C ⟩)
      → ⟨ (interpR p ∘R interpR q) x z ⟩ → ⟨ interpR (p ++ q) x z ⟩
  ++← nil        q x z = PT.rec (isProp⟨⟩ (interpR q x z)) λ
    { (y , xy , h) → subst (λ t → ⟨ interpR q t z ⟩) (sym xy) h }
  ++← (cons e p) q x z = PT.rec isPropPropTrunc λ
    { (w , h1 , hq) → PT.rec isPropPropTrunc (λ { (y , Exy , hp) → ∣ y , Exy , ++← p q y z ∣ w , hp , hq ∣₁ ∣₁ }) h1 }

  -- Interpretation turns route concatenation into composition of relations.
  interp-++ : ∀ {A B C} (p : Route A B) (q : Route B C) → interpR (p ++ q) ≡ interpR p ∘R interpR q
  interp-++ p q = funExt λ x → funExt λ z → ⇔toPath (++→ p q x z) (++← p q x z)

  -- Equivalent routes (under sound rules) have equal interpretations.
  sound≈ : SoundRules → ∀ {A B} {r s : Route A B} → r ≈ s → interpR r ≡ interpR s
  sound≈ sr ≈-refl        = refl
  sound≈ sr (≈-sym h)     = sym (sound≈ sr h)
  sound≈ sr (≈-trans h k) = sound≈ sr h ∙ sound≈ sr k
  sound≈ sr (≈-step ρ p s) =
      interp-++ p (lhs ρ ++ s)
    ∙ cong (λ t → interpR p ∘R t)
        (interp-++ (lhs ρ) s ∙ cong (λ t → t ∘R interpR s) (sr ρ) ∙ sym (interp-++ (rhs ρ) s))
    ∙ sym (interp-++ p (rhs ρ ++ s))

  -- T6 (proved).
  routeIndependence : RouteIndependence
  routeIndependence = sound≈

  -- The interpretation descends to Coe: the meaning of a coercion class.
  interpC : SoundRules → ∀ {A B} → Coe A B → ⟨ Car A ⟩ → ⟨ Car B ⟩ → hProp ℓ-zero
  interpC sr = SQ.rec (isSetΠ2 λ _ _ → isSetHProp) interpR (λ r s h → sound≈ sr h)
