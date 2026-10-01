{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- T7, complete. A normalizer for routes from the critical-pair conditions alone.
-- Left-hand and right-hand sides are read as lists of edge names. Termination follows from the rules
-- shortening routes, local confluence from the critical-pair lemma (Metonymy.StringRewriting), and the
-- redex search from the finiteness of the rule list. Rewriting on names is lifted back to typed routes with
-- Metonymy.TypedFactor, and the result is a Normalizer in the sense of Metonymy.Equivalence, so equivalence
-- of routes is decidable and the readings are exactly the normal forms.
-- Hypotheses: the rule list is finite and complete, every rule shortens the route, and the critical pairs
-- (overlaps and inclusions of left-hand sides) are joinable. These are finite checks on the lexicon.
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.NormalizeFull (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (¬-<-zero ; _<_)
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
import Cubical.Data.Empty as E

open Lexicon L
open Routes graph using (Route ; nil ; cons) renaming (_++_ to _++ʳ_)
open Rules R
open Equiv graph R
open Checker L
open import Metonymy.Equivalence graph R using (Normalizer)
import Metonymy.Enumerate L as En
import Metonymy.TypedFactor L as TF
open TF using (names-++)
open TF.Factor R using (factor-lhs)
import Metonymy.StringRewriting as SR

-- Rules read as rewriting on lists of edge names.
lhsN rhsN : RuleId → List ℕ
lhsN ρ = routeNames (lhs ρ)
rhsN ρ = routeNames (rhs ρ)

module S = SR RuleId lhsN rhsN

-- Lifting rewriting on names to typed routes needs only that left-hand sides have at least one edge.
module LiftSteps (ne : ∀ ρ → lhsN ρ ≡ [] → E.⊥) where

  -- One step of rewriting on the names of a route is a step of the typed equivalence.
  lift-step : ∀ {A B} (r : Route A B) {v} → routeNames r S.⇒s v
            → Σ (Route A B) (λ s → (routeNames s ≡ v) × (r ≈ s))
  lift-step r (ρ , p , t , er , ev) with factor-lhs ρ (ne ρ) r p t er
  ... | pp , tt , req , np , nt =
    (pp ++ʳ (rhs ρ ++ʳ tt))
    , (names-++ pp (rhs ρ ++ʳ tt) ∙ cong₂ _++_ np (names-++ (rhs ρ) tt ∙ cong (rhsN ρ ++_) nt) ∙ sym ev)
    , subst (λ x → x ≈ (pp ++ʳ (rhs ρ ++ʳ tt))) (sym req) (≈-step ρ pp tt)

  lift-chain : ∀ {A B} (r : Route A B) {u v} → routeNames r ≡ u → u S.→* v
             → Σ (Route A B) (λ s → (routeNames s ≡ v) × (r ≈ s))
  lift-chain r e S.ε = r , e , ≈-refl
  lift-chain r e (st S.▹ rest) with lift-step r (S.step≡ e refl st)
  ... | s1 , ns1 , r≈s1 with lift-chain s1 ns1 rest
  ...   | s2 , ns2 , s1≈s2 = s2 , ns2 , ≈-trans r≈s1 s1≈s2

  -- The typed equivalence is contained in the equivalence closure of rewriting on names.
  ≈⇒↔*S : ∀ {A B} {r s : Route A B} → r ≈ s → routeNames r S.↔* routeNames s
  ≈⇒↔*S ≈-refl        = S.↔-refl
  ≈⇒↔*S (≈-sym h)     = S.↔-sym (≈⇒↔*S h)
  ≈⇒↔*S (≈-trans h k) = S.↔-trans (≈⇒↔*S h) (≈⇒↔*S k)
  ≈⇒↔*S (≈-step ρ p t) =
    subst2 (λ a b → a S.↔* b)
      (sym (names-++ p (lhs ρ ++ʳ t) ∙ cong (routeNames p ++_) (names-++ (lhs ρ) t)))
      (sym (names-++ p (rhs ρ ++ʳ t) ∙ cong (routeNames p ++_) (names-++ (rhs ρ) t)))
      (S.↔-step (S.intro ρ (routeNames p) (routeNames t)))


module Build
  (rules : List RuleId) (rules-complete : ∀ ρ → S.Mem ρ rules)
  (sh : S.Shrinks)
  (CP₁ : ∀ ρa ρb u v x → lhsN ρb ≡ u ++ v → lhsN ρa ≡ v ++ x → S.Joinable (u ++ rhsN ρa) (rhsN ρb ++ x))
  (CP₂ : ∀ ρa ρb u y → lhsN ρb ≡ u ++ (lhsN ρa ++ y) → S.Joinable (u ++ (rhsN ρa ++ y)) (rhsN ρb))
  where

  module Q  = S.Search rules rules-complete
  module NN = Q.Norm sh CP₁ CP₂

  -- A shortening rule has a left-hand side with at least one edge.
  ne : ∀ ρ → lhsN ρ ≡ [] → E.⊥
  ne ρ h = ¬-<-zero (subst (λ l → length (rhsN ρ) < length l) h (sh ρ))

  open LiftSteps ne

  -- The normalizer.
  normalizer : Normalizer
  normalizer = record
    { routeEq   = En.routeEq
    ; norm      = λ r → fst (lift-chain r refl (NN.normS-reduces (routeNames r)))
    ; norm≈     = λ r → snd (snd (lift-chain r refl (NN.normS-reduces (routeNames r))))
    ; norm-resp = λ {A} {B} {r} {s} h →
        En.routeNames-inj
          (fst (snd (lift-chain r refl (NN.normS-reduces (routeNames r))))
           ∙ NN.normS-resp (≈⇒↔*S h)
           ∙ sym (fst (snd (lift-chain s refl (NN.normS-reduces (routeNames s))))))
    }
