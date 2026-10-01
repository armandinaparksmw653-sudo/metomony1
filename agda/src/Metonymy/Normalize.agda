{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- T7. A normalizer from checkable conditions.
-- Orient each declared equivalence left to right. If every rule shortens the route (termination, proved
-- from the length measure), the one-step rewriting is locally confluent (the critical-pair condition,
-- a finite check supplied by the lexicon) and reducibility is decidable (a finite search over rules),
-- then equivalence of routes is decidable and the readings are exactly the normal forms (Metonymy.Equivalence).
-- Newman's lemma and Church-Rosser are proved in Metonymy.Rewriting.
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Normalize (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-suc)
open import Cubical.Data.Nat.Order
open import Cubical.Relation.Nullary using (Dec)
import Cubical.Data.Empty as E
import Metonymy.Rewriting as Rew

open Lexicon L
open Routes graph
open Rules R
open Equiv graph R
open import Metonymy.Equivalence graph R using (Normalizer)
import Metonymy.Enumerate L as En

-- One step of oriented rewriting, anywhere in a route.
infix 4 _⇒_
data _⇒_ {A B : Ty} : Route A B → Route A B → Type where
  rw : ∀ (ρ : RuleId) (p : Route A (rsrc ρ)) (s : Route (rtgt ρ) B)
     → (p ++ (lhs ρ ++ s)) ⇒ (p ++ (rhs ρ ++ s))

-- The abstract rewriting theory instantiated at routes from A to B.
module RW (A B : Ty) = Rew {Route A B} (_⇒_ {A} {B})

------------------------------------------------------------------------------
-- Rewriting versus the declared equivalence

⇒⊆≈ : ∀ {A B} {r s : Route A B} → r ⇒ s → r ≈ s
⇒⊆≈ (rw ρ p s) = ≈-step ρ p s

⇒*⊆≈ : ∀ {A B} {r s : Route A B} → RW._→*_ A B r s → r ≈ s
⇒*⊆≈ RW.ε       = ≈-refl
⇒*⊆≈ (st RW.▹ rest) = ≈-trans (⇒⊆≈ st) (⇒*⊆≈ rest)

≈⊆↔* : ∀ {A B} {r s : Route A B} → r ≈ s → RW._↔*_ A B r s
≈⊆↔* ≈-refl        = RW.↔-refl
≈⊆↔* (≈-sym h)     = RW.↔-sym (≈⊆↔* h)
≈⊆↔* (≈-trans h k) = RW.↔-trans (≈⊆↔* h) (≈⊆↔* k)
≈⊆↔* (≈-step ρ p s) = RW.↔-step (rw ρ p s)

------------------------------------------------------------------------------
-- Termination from a shrinking measure

len : ∀ {A B} → Route A B → ℕ
len nil        = 0
len (cons e r) = suc (len r)

len-++ : ∀ {A B C} (p : Route A B) (q : Route B C) → len (p ++ q) ≡ len p + len q
len-++ nil        q = refl
len-++ (cons e p) q = cong suc (len-++ p q)

-- Every rule makes the route strictly shorter.
Shrinks : Type
Shrinks = ∀ ρ → len (rhs ρ) < len (lhs ρ)

step-shrinks : Shrinks → ∀ {A B} {r s : Route A B} → r ⇒ s → len s < len r
step-shrinks sh (rw ρ p t) =
  subst (λ n → suc n ≤ len (p ++ (lhs ρ ++ t))) (sym (eqR ρ p t))
    (subst (λ n → suc (len p + (len (rhs ρ) + len t)) ≤ n) (sym (eqL ρ p t))
      (subst (_≤ len p + (len (lhs ρ) + len t)) (+-suc (len p) (len (rhs ρ) + len t))
        (≤-k+ {k = len p} (≤-+k {k = len t} (sh ρ)))))
  where
    eqR : ∀ ρ p t → len (p ++ (rhs ρ ++ t)) ≡ len p + (len (rhs ρ) + len t)
    eqR ρ p t = len-++ p (rhs ρ ++ t) ∙ cong (len p +_) (len-++ (rhs ρ) t)

    eqL : ∀ ρ p t → len (p ++ (lhs ρ ++ t)) ≡ len p + (len (lhs ρ) + len t)
    eqL ρ p t = len-++ p (lhs ρ ++ t) ∙ cong (len p +_) (len-++ (lhs ρ) t)

snLen : Shrinks → ∀ {A B} (n : ℕ) (r : Route A B) → len r ≤ n → RW.SN A B r
snLen sh zero    r h = RW.sn (λ s st → E.rec (¬-<-zero (≤-trans (step-shrinks sh st) h)))
snLen sh (suc n) r h = RW.sn (λ s st → snLen sh n s (pred-≤-pred (≤-trans (step-shrinks sh st) h)))

terminates : Shrinks → ∀ {A B} (r : Route A B) → RW.SN A B r
terminates sh r = snLen sh (len r) r ≤-refl

------------------------------------------------------------------------------
-- The normalizer

module Build
  (sh : Shrinks)
  (LC : ∀ {A B} {r s₁ s₂ : Route A B} → r ⇒ s₁ → r ⇒ s₂ → RW.Joinable A B s₁ s₂)
  (step? : ∀ {A B} (r : Route A B) → Dec (Σ (Route A B) (λ s → r ⇒ s)))
  where

  module NN (A B : Ty) = RW.Normalize A B (step? {A} {B})

  normalizer : Normalizer
  normalizer = record
    { routeEq   = En.routeEq
    ; norm      = λ {A} {B} r → NN.norm A B LC (terminates sh) r
    ; norm≈     = λ {A} {B} r → ⇒*⊆≈ (NN.norm-reduces A B LC (terminates sh) r)
    ; norm-resp = λ {A} {B} {r} {s} h → NN.norm-resp A B LC (terminates sh) (≈⊆↔* h)
    }
