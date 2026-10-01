{-# OPTIONS --safe --cubical --guardedness #-}

-- T17. Lexicon audit by computation.
-- A finite model gives every sense type an enumerated carrier and every edge a Boolean table.
-- A Boolean evaluator of routes is proved equivalent to the relational semantics, so checking that every
-- declared equivalence holds in the finite model (a finite computation) proves SoundRules for it.
open import Metonymy.Graph

module Metonymy.Audit (G : Graph) (R : Rules G) where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_ ; _or_ ; false≢true ; isSetBool)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Empty as E
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete)
open import Cubical.Relation.Nullary.Properties using (Discrete→isSet)
open import Cubical.Functions.Logic
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁)

open Graph G
open Routes G
open Rules R
open import Metonymy.Semantics G R

------------------------------------------------------------------------------
-- Finite lists: membership, any, all

data Mem {X : Type} (x : X) : List X → Type where
  here  : ∀ {xs} → Mem x (x ∷ xs)
  there : ∀ {y xs} → Mem x xs → Mem x (y ∷ xs)

anyL : ∀ {X : Type} → (X → Bool) → List X → Bool
anyL p []       = false
anyL p (x ∷ xs) = p x or anyL p xs

allL : ∀ {X : Type} → (X → Bool) → List X → Bool
allL p []       = true
allL p (x ∷ xs) = p x and allL p xs

private
  or-true-right : ∀ a → a or true ≡ true
  or-true-right true  = refl
  or-true-right false = refl

  and-true : ∀ x y → x and y ≡ true → (x ≡ true) × (y ≡ true)
  and-true true  true  _ = refl , refl
  and-true true  false p = E.rec (false≢true p)
  and-true false y     p = E.rec (false≢true p)

  and-intro : ∀ x y → x ≡ true → y ≡ true → x and y ≡ true
  and-intro true true _ _ = refl
  and-intro true false _ q = E.rec (false≢true q)
  and-intro false y p _ = E.rec (false≢true p)

anyL-sound : ∀ {X : Type} (p : X → Bool) (xs : List X) → anyL p xs ≡ true → Σ X (λ x → p x ≡ true)
anyL-sound p []       h = E.rec (false≢true h)
anyL-sound p (x ∷ xs) h = go (p x) refl h
  where
    go : (b : Bool) → p x ≡ b → b or anyL p xs ≡ true → Σ _ (λ y → p y ≡ true)
    go true  eq _  = x , eq
    go false eq h' = anyL-sound p xs h'

anyL-complete : ∀ {X : Type} (p : X → Bool) {x : X} {xs : List X} → Mem x xs → p x ≡ true → anyL p xs ≡ true
anyL-complete p {x} (here {xs}) px = subst (λ b → b or anyL p xs ≡ true) (sym px) refl
anyL-complete p {x} (there {y} {xs} m) px = cong (λ t → p y or t) (anyL-complete p m px) ∙ or-true-right (p y)

allL-sound : ∀ {X : Type} (p : X → Bool) {x : X} {xs : List X} → allL p xs ≡ true → Mem x xs → p x ≡ true
allL-sound p {x} h here        = fst (and-true (p x) _ h)
allL-sound p {x} h (there {y} m) = allL-sound p (snd (and-true (p y) _ h)) m

------------------------------------------------------------------------------
-- Finite models

record FinModel : Type₁ where
  field
    Elem           : Ty → Type
    elemEq         : ∀ A → Discrete (Elem A)
    elems          : ∀ A → List (Elem A)
    elems-complete : ∀ A (x : Elem A) → Mem x (elems A)
    tab            : (e : EdgeId) → Elem (src e) → Elem (tgt e) → Bool

toModel : FinModel → Model
toModel F = record
  { Car     = λ A → Elem A , Discrete→isSet (elemEq A)
  ; EdgeRel = λ e x y → (tab e x y ≡ true) , isSetBool _ _
  }
  where open FinModel F

module _ (F : FinModel) where
  open FinModel F

  decB : ∀ {A : Type} → Dec A → Bool
  decB (yes _) = true
  decB (no _)  = false

  -- Boolean evaluation of a route.
  evalR : ∀ {A B} → Route A B → Elem A → Elem B → Bool
  evalR {A} nil x y = decB (elemEq A x y)
  evalR (cons e r) x z = anyL (λ y → tab e x y and evalR r y z) (elems (tgt e))

  -- The evaluator agrees with the relational semantics.
  evalR⇒ : ∀ {A B} (r : Route A B) (x : Elem A) (y : Elem B) → evalR r x y ≡ true → ⟨ interpR (toModel F) r x y ⟩
  evalR⇒ {A} nil x y h with elemEq A x y
  ... | yes p = p
  ... | no  _ = E.rec (false≢true h)
  evalR⇒ (cons e r) x z h with anyL-sound _ (elems (tgt e)) h
  ... | y , hy with and-true (tab e x y) (evalR r y z) hy
  ... | h1 , h2 = ∣ y , h1 , evalR⇒ r y z h2 ∣₁

  ⇒evalR : ∀ {A B} (r : Route A B) (x : Elem A) (y : Elem B) → ⟨ interpR (toModel F) r x y ⟩ → evalR r x y ≡ true
  ⇒evalR {A} nil x y p with elemEq A x y
  ... | yes _ = refl
  ... | no ¬p = E.rec (¬p p)
  ⇒evalR (cons e r) x z = PT.rec (isSetBool _ _) λ { (y , h1 , h2) →
    anyL-complete _ (elems-complete (tgt e) y) (and-intro _ _ h1 (⇒evalR r y z h2)) }

  -- Boolean equality.
  eqB : Bool → Bool → Bool
  eqB true  true  = true
  eqB false false = true
  eqB _     _     = false

  eqB-sound : ∀ a b → eqB a b ≡ true → a ≡ b
  eqB-sound true  true  _ = refl
  eqB-sound false false _ = refl
  eqB-sound true  false h = E.rec (false≢true h)
  eqB-sound false true  h = E.rec (false≢true h)

  eqB-refl : ∀ a → eqB a a ≡ true
  eqB-refl true  = refl
  eqB-refl false = refl

  -- Audit of one declared equivalence: both sides relate exactly the same pairs of referents.
  auditRule : RuleId → Bool
  auditRule ρ = allL (λ x → allL (λ y → eqB (evalR (lhs ρ) x y) (evalR (rhs ρ) x y)) (elems (rtgt ρ)))
                     (elems (rsrc ρ))

  -- T17. A passed audit proves the equivalence semantically valid in the finite model.
  audit-sound : ∀ ρ → auditRule ρ ≡ true → interpR (toModel F) (lhs ρ) ≡ interpR (toModel F) (rhs ρ)
  audit-sound ρ h = funExt λ x → funExt λ y →
    let pt : eqB (evalR (lhs ρ) x y) (evalR (rhs ρ) x y) ≡ true
        pt = allL-sound _ (allL-sound _ h (elems-complete (rsrc ρ) x)) (elems-complete (rtgt ρ) y)
        eq : evalR (lhs ρ) x y ≡ evalR (rhs ρ) x y
        eq = eqB-sound _ _ pt
    in ⇔toPath (λ p → evalR⇒ (rhs ρ) x y (sym eq ∙ ⇒evalR (lhs ρ) x y p))
               (λ p → evalR⇒ (lhs ρ) x y (eq ∙ ⇒evalR (rhs ρ) x y p))

  -- If every declared equivalence passes the audit, the finite model validates all of them.
  audit-all : (∀ ρ → auditRule ρ ≡ true) → SoundRules (toModel F)
  audit-all pass ρ = audit-sound ρ (pass ρ)
