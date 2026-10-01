{-# OPTIONS --safe --cubical --guardedness #-}

-- Distinguishing and classifying readings.
--   T18: an apartness witness (a pair of referents on which two routes differ) proves the routes are
--        not equivalent, and that they are different points of Coe. Purely positive evidence.
--   T7:  if the lexicon supplies a normalizer (a terminating, confluent presentation of the declared
--        equivalences, as data), then equivalence is decidable and the readings are exactly the normal forms.
open import Metonymy.Graph

module Metonymy.Equivalence (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as E using ()
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete ; ¬_)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/ ; squash/ ; elimProp)

open Graph G
open Routes G
open Rules R
open Equiv G R
open import Metonymy.Semantics G R

------------------------------------------------------------------------------
-- T18. Apartness of readings

module _ (M : Model) (sr : SoundRules M) where
  open Model M

  -- r and s are apart: some pair of referents is related by r but not by s.
  Apart : ∀ {A B} → Route A B → Route A B → Type
  Apart {A} {B} r s = Σ ⟨ Car A ⟩ (λ x → Σ ⟨ Car B ⟩ (λ y → ⟨ interpR M r x y ⟩ × (¬ ⟨ interpR M s x y ⟩)))

  apart⇒¬≈ : ∀ {A B} {r s : Route A B} → Apart r s → ¬ (r ≈ s)
  apart⇒¬≈ (x , y , hr , ns) h = ns (subst (λ f → ⟨ f x y ⟩) (sound≈ M sr h) hr)

  -- Apart routes are distinct points of the set of readings Coe A B.
  apart⇒distinct : ∀ {A B} {r s : Route A B} → Apart r s → ¬ ([ r ] ≡ [ s ])
  apart⇒distinct (x , y , hr , ns) p =
    ns (subst (λ f → ⟨ f x y ⟩) (cong (λ q → interpC M sr q) p) hr)

------------------------------------------------------------------------------
-- T7. Classification of readings by normal forms

-- A normalizer: decidable equality of routes and a normal-form function respecting the equivalence.
record Normalizer : Type where
  field
    routeEq   : ∀ {A B} → Discrete (Route A B)
    norm      : ∀ {A B} → Route A B → Route A B
    norm≈     : ∀ {A B} (r : Route A B) → r ≈ norm r
    norm-resp : ∀ {A B} {r s : Route A B} → r ≈ s → norm r ≡ norm s

module _ (N : Normalizer) where
  open Normalizer N

  -- Equivalence of routes is decidable.
  decEquiv : ∀ {A B} (r s : Route A B) → Dec (r ≈ s)
  decEquiv r s with routeEq (norm r) (norm s)
  ... | yes p = yes (≈-trans (norm≈ r) (≈-trans (subst (λ t → norm r ≈ t) p ≈-refl) (≈-sym (norm≈ s))))
  ... | no ¬p = no (λ h → ¬p (norm-resp h))

  norm-idem : ∀ {A B} (r : Route A B) → norm (norm r) ≡ norm r
  norm-idem r = sym (norm-resp (norm≈ r))

  NormalForm : Ty → Ty → Type
  NormalForm A B = Σ (Route A B) (λ r → norm r ≡ r)

  isSetRoute : ∀ {A B} → isSet (Route A B)
  isSetRoute = Discrete→isSet routeEq

  isSetNormalForm : ∀ {A B} → isSet (NormalForm A B)
  isSetNormalForm = isSetΣ isSetRoute (λ r → isProp→isSet (isSetRoute _ _))

  -- The readings of a coercion are exactly the normal forms.
  classification : ∀ {A B} → Coe A B ≃ NormalForm A B
  classification {A} {B} = isoToEquiv (iso fun inv sec ret)
    where
      fun : Coe A B → NormalForm A B
      fun = SQ.rec isSetNormalForm (λ r → norm r , norm-idem r)
              (λ r s h → Σ≡Prop (λ t → isSetRoute _ _) (norm-resp h))

      inv : NormalForm A B → Coe A B
      inv (r , _) = [ r ]

      sec : ∀ n → fun (inv n) ≡ n
      sec (r , p) = Σ≡Prop (λ t → isSetRoute _ _) p

      ret : ∀ q → inv (fun q) ≡ q
      ret = elimProp (λ q → squash/ _ _) (λ r → eq/ (norm r) r (≈-sym (norm≈ r)))
