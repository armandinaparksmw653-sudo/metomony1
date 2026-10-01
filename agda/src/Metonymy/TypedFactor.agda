{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Decomposing typed routes. If the names of a route contain the names of a rule's left-hand side, the route
-- itself factors as prefix ++ lhs ++ suffix with the prefix and suffix again typed routes. The proof avoids
-- matching two indexed routes against each other: routes are split one at a time, and the ends of two routes
-- with the same names are compared with a heterogeneous lemma.
open import Agda.Builtin.Maybe
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.TypedFactor (L : Lexicon) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_)
open import Cubical.Data.List.Properties using (cons-inj₁ ; cons-inj₂ ; ¬cons≡nil ; ¬nil≡cons)
import Cubical.Data.Empty as E
import Agda.Builtin.Equality as B

open Lexicon L
open Routes graph using (Route ; nil ; cons) renaming (_++_ to _++ʳ_)
open Checker L

private
  toPath : ∀ {ℓ} {X : Type ℓ} {x y : X} → x B.≡ y → x ≡ y
  toPath B.refl = refl

  fromJust : ∀ {X : Type} → X → Maybe X → X
  fromJust d nothing  = d
  fromJust d (just x) = x

-- Edge names determine edges.
edgeName-inj : ∀ {e e'} → edgeName e ≡ edgeName e' → e ≡ e'
edgeName-inj {e} {e'} p =
  cong (fromJust e) (sym (toPath (edgeOf-name e)) ∙ cong edgeOf p ∙ toPath (edgeOf-name e'))

-- Names of a concatenation.
names-++ : ∀ {A B C} (p : Route A B) (q : Route B C) → routeNames (p ++ʳ q) ≡ routeNames p ++ routeNames q
names-++ nil        q = refl
names-++ (cons e p) q = cong (edgeName e ∷_) (names-++ p q)

-- A route with no edges joins equal types.
names-empty : ∀ {A B} (r : Route A B) → routeNames r ≡ [] → A ≡ B
names-empty nil        _ = refl
names-empty (cons e r) h = E.rec (¬cons≡nil h)

------------------------------------------------------------------------------
-- Splitting a typed route along a split of its names

split : ∀ {A B} (r : Route A B) (xs ys : List ℕ) → routeNames r ≡ xs ++ ys
      → Σ Ty (λ M → Σ (Route A M) (λ p → Σ (Route M B) (λ q →
          (routeNames p ≡ xs) × (routeNames q ≡ ys) × (r ≡ p ++ʳ q))))
split nil [] ys h = _ , nil , nil , refl , h , refl
split nil (x ∷ xs) ys h = E.rec (¬nil≡cons h)
split (cons e r) [] ys h = _ , nil , cons e r , refl , h , refl
split (cons e r) (x ∷ xs) ys h with split r xs ys (cons-inj₂ h)
... | M , p , q , hp , hq , hr =
  M , cons e p , q , cong₂ _∷_ (cons-inj₁ h) hp , hq , cong (cons e) hr

------------------------------------------------------------------------------
-- Comparing the ends of two routes with the same names

ends-eq : ∀ {A B A' B'} (p : Route A B) (p' : Route A' B') → routeNames p ≡ routeNames p'
        → ((A ≡ A') × (B ≡ B')) ⊎ (routeNames p ≡ [])
ends-eq nil nil h = inr refl
ends-eq nil (cons e' p') h = inr refl
ends-eq (cons e p) nil h = E.rec (¬cons≡nil h)
ends-eq {B = B} {B' = B'} (cons e p) (cons e' p') h with ends-eq p p' (cons-inj₂ h)
... | inl (st , tg) = inl (cong (λ x → Lexicon.src L x) (edgeName-inj (cons-inj₁ h)) , tg)
... | inr pe =
  inl ( cong (λ x → Lexicon.src L x) (edgeName-inj (cons-inj₁ h))
      , sym (names-empty p pe) ∙ cong (λ x → Lexicon.tgt L x) (edgeName-inj (cons-inj₁ h))
        ∙ names-empty p' (sym (cons-inj₂ h) ∙ pe) )

------------------------------------------------------------------------------
-- Factoring a route along the left-hand side of a rule

import Metonymy.Enumerate L as En

module Factor (R : Rules graph) where
  open Rules R

  -- Replace the middle types by those of the rule, using the equalities of the ends.
  subst-ends : ∀ {A B} (ρ : RuleId) (M M2 : Ty) (p0 : Route A M) (p2 : Route M M2) (q2 : Route M2 B)
             → rsrc ρ ≡ M → rtgt ρ ≡ M2 → routeNames p2 ≡ routeNames (lhs ρ)
             → Σ (Route A (rsrc ρ)) (λ p → Σ (Route (rtgt ρ) B) (λ t →
                 (p ++ʳ (lhs ρ ++ʳ t) ≡ p0 ++ʳ (p2 ++ʳ q2)) × (routeNames p ≡ routeNames p0) × (routeNames t ≡ routeNames q2)))
  subst-ends {A} {B} ρ M M2 p0 p2 q2 eM eM2 hn =
    J (λ M' _ → ∀ (M2' : Ty) (p0' : Route A M') (p2' : Route M' M2') (q2' : Route M2' B)
              → rtgt ρ ≡ M2' → routeNames p2' ≡ routeNames (lhs ρ)
              → Σ (Route A (rsrc ρ)) (λ p → Σ (Route (rtgt ρ) B) (λ t →
                  (p ++ʳ (lhs ρ ++ʳ t) ≡ p0' ++ʳ (p2' ++ʳ q2')) × (routeNames p ≡ routeNames p0') × (routeNames t ≡ routeNames q2'))))
      (λ M2' p0' p2' q2' e2 hn' →
         J (λ M2'' _ → ∀ (p2'' : Route (rsrc ρ) M2'') (q2'' : Route M2'' B) → routeNames p2'' ≡ routeNames (lhs ρ)
              → Σ (Route A (rsrc ρ)) (λ p → Σ (Route (rtgt ρ) B) (λ t →
                  (p ++ʳ (lhs ρ ++ʳ t) ≡ p0' ++ʳ (p2'' ++ʳ q2'')) × (routeNames p ≡ routeNames p0') × (routeNames t ≡ routeNames q2''))))
           (λ p2'' q2'' hn'' → p0' , q2'' , cong (λ x → p0' ++ʳ (x ++ʳ q2'')) (sym (En.routeNames-inj hn''))
                                 , refl , refl)
           e2 p2' q2' hn')
      eM M2 p0 p2 q2 eM2 hn

  -- If the names of a route contain the left-hand side of a rule (which has at least one edge),
  -- the route factors through the rule.
  factor-lhs : ∀ {A B} (ρ : RuleId) → (routeNames (lhs ρ) ≡ [] → E.⊥) → (r : Route A B) (xs ys : List ℕ)
             → routeNames r ≡ xs ++ (routeNames (lhs ρ) ++ ys)
             → Σ (Route A (rsrc ρ)) (λ p → Σ (Route (rtgt ρ) B) (λ t →
                 (r ≡ p ++ʳ (lhs ρ ++ʳ t)) × (routeNames p ≡ xs) × (routeNames t ≡ ys)))
  factor-lhs ρ ne r xs ys h with split r xs (routeNames (lhs ρ) ++ ys) h
  ... | M , p0 , q , hp0 , hq , hr with split q (routeNames (lhs ρ)) ys hq
  ...   | M2 , p2 , q2 , hp2 , hq2 , hqr with ends-eq p2 (lhs ρ) hp2
  ...     | inr e0 = E.rec (ne (sym hp2 ∙ e0))
  ...     | inl (eM , eM2) with subst-ends ρ M M2 p0 p2 q2 (sym eM) (sym eM2) hp2
  ...       | p , t , eq , np , nt =
    p , t , (hr ∙ cong (p0 ++ʳ_) hqr ∙ sym eq) , (np ∙ hp0) , (nt ∙ hq2)
