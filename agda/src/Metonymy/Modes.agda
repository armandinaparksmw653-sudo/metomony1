{-# OPTIONS --safe --cubical --guardedness #-}

-- Interpretation modes over the set of readings Coe A B.
--   T9':  Every reading => a fixed reading => some reading; Resolve => Reading.
--   T10:  Retain (truncated existence) is irreversible: a retraction of the truncation forces a proposition.
--   T11:  a homonymous word cannot be both of its senses at once (disjointness of the sum).
open import Metonymy.Graph

module Metonymy.Modes (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
import Cubical.Data.Empty as E
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to inlS ; inr to inrS)
open import Cubical.Functions.Logic
open import Cubical.HITs.SetQuotients as SQ using ([_])
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R

module _ (M : Model) (sr : SoundRules M) where
  open Model M

  ---------------------------------------------------------------------------
  -- The meaning of a sentence under a fixed reading class k.

  Reading : ∀ {A B} → Coe A B → (⟨ Car B ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  Reading k P x = ∃[ y ∶ _ ] (interpC M sr k x y ⊓ P y)

  -- Weak: some reading is true. Strong: every reading is true.
  SomeReading EveryReading : ∀ {A B} → (⟨ Car B ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  SomeReading  {A} {B} P x = ∃[ k ∶ Coe A B ] Reading k P x
  EveryReading {A} {B} P x = ∀[ k ∶ Coe A B ] Reading k P x

  -- Resolve at a reading class and a referent.
  ResolveC : ∀ {A B} → Coe A B → ⟨ Car B ⟩ → (⟨ Car B ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  ResolveC k y P x = interpC M sr k x y ⊓ P y

  -- T9' (lattice of modes).
  every⇒reading : ∀ {A B} (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩) (k : Coe A B)
                → ⟨ EveryReading P x ⟩ → ⟨ Reading k P x ⟩
  every⇒reading P x k h = h k

  reading⇒some : ∀ {A B} (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩) (k : Coe A B)
               → ⟨ Reading k P x ⟩ → ⟨ SomeReading P x ⟩
  reading⇒some P x k h = ∣ k , h ∣₁

  resolve⇒reading : ∀ {A B} (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩) (k : Coe A B) (y : ⟨ Car B ⟩)
                  → ⟨ ResolveC k y P x ⟩ → ⟨ Reading k P x ⟩
  resolve⇒reading P x k y h = ∣ y , h ∣₁

  -- The class meaning agrees with the route meaning on representatives.
  reading-rep : ∀ {A B} (r : Route A B) (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩)
              → Reading [ r ] P x ≡ Retain M r P x
  reading-rep r P x = refl

  -- Retain does not depend on the chosen representative of the class.
  retain-indep : ∀ {A B} {r s : Route A B} (P : ⟨ Car B ⟩ → hProp ℓ-zero) (x : ⟨ Car A ⟩)
               → r ≈ s → Retain M r P x ≡ Retain M s P x
  retain-indep {r = r} {s = s} P x h = cong (λ f → ∃[ y ∶ _ ] (f x y ⊓ P y)) (sound≈ M sr h)

------------------------------------------------------------------------------
-- T10. Irreversibility of Retain.
-- A retraction of the truncation map exists exactly when the fibre is a proposition: if several
-- distinct referents are reachable, no canonical choice can be extracted from the truncated meaning.

retraction⇒isProp : ∀ {ℓ} {X : Type ℓ} (s : ∥ X ∥₁ → X) → (∀ x → s ∣ x ∣₁ ≡ x) → isProp X
retraction⇒isProp s ret x y = sym (ret x) ∙ cong s (isPropPropTrunc ∣ x ∣₁ ∣ y ∣₁) ∙ ret y

noChoice : ∀ {ℓ} {X : Type ℓ} (a b : X) → (a ≡ b → E.⊥) → (s : ∥ X ∥₁ → X) → (∀ x → s ∣ x ∣₁ ≡ x) → E.⊥
noChoice a b a≢b s ret = a≢b (retraction⇒isProp s ret a b)

------------------------------------------------------------------------------
-- T11. A homonymous word has a sum of senses; a single referent is never of both senses.

module _ {ℓ} (S₁ S₂ : Type ℓ) where

  IsSense₁ IsSense₂ : S₁ ⊎ S₂ → Type ℓ
  IsSense₁ z = Σ S₁ (λ x → z ≡ inlS x)
  IsSense₂ z = Σ S₂ (λ y → z ≡ inrS y)

  private
    isL : S₁ ⊎ S₂ → Type
    isL (inlS _) = Unit
    isL (inrS _) = E.⊥

  inl≢inr : ∀ {x : S₁} {y : S₂} → inlS x ≡ inrS y → E.⊥
  inl≢inr p = subst isL p tt

  homonym-disjoint : ∀ z → IsSense₁ z → IsSense₂ z → E.⊥
  homonym-disjoint z (x , px) (y , py) = inl≢inr (sym px ∙ py)

------------------------------------------------------------------------------
-- T11 (Conjoin). Two coercions of one source applied to the same referent. The common source is enforced
-- by the typing of Conjoin itself; for a homonym (disjoint senses) the conjunction is refutable.

module _ (M : Model) where
  open Model M

  Conjoin : ∀ {A B C} → Route A B → (⟨ Car B ⟩ → hProp ℓ-zero)
          → Route A C → (⟨ Car C ⟩ → hProp ℓ-zero) → ⟨ Car A ⟩ → hProp ℓ-zero
  Conjoin r P s Q x = Retain M r P x ⊓ Retain M s Q x

  conjoin⇒first : ∀ {A B C} (r : Route A B) P (s : Route A C) Q x → ⟨ Conjoin r P s Q x ⟩ → ⟨ Retain M r P x ⟩
  conjoin⇒first r P s Q x = fst

  conjoin⇒second : ∀ {A B C} (r : Route A B) P (s : Route A C) Q x → ⟨ Conjoin r P s Q x ⟩ → ⟨ Retain M s Q x ⟩
  conjoin⇒second r P s Q x = snd

  -- If the first coercion only applies to referents of one sense and the second only to referents of a
  -- disjoint sense, no referent satisfies the conjunction.
  conjoin-impossible : ∀ {A B C} (r : Route A B) P (s : Route A C) Q (IsL IsR : ⟨ Car A ⟩ → Type)
                     → (∀ z → IsL z → IsR z → E.⊥)
                     → (∀ z y → ⟨ interpR M r z y ⟩ → IsL z)
                     → (∀ z y → ⟨ interpR M s z y ⟩ → IsR z)
                     → ∀ z → ⟨ Conjoin r P s Q z ⟩ → E.⊥
  conjoin-impossible r P s Q IsL IsR disj supL supR z (h1 , h2) =
    PT.rec E.isProp⊥ (λ { (y , a , _) →
      PT.rec E.isProp⊥ (λ { (y' , b , _) → disj z (supL z y a) (supR z y' b) }) h2 }) h1
