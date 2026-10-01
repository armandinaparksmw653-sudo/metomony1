{-# OPTIONS --safe --cubical-compatible #-}

-- A deliberately non-confluent lexicon: e1;e2 is declared equivalent to two different direct edges e3 and e4.
module Metonymy.ExampleRulesBad where

open import Metonymy.Base
open import Metonymy.Graph
open import Metonymy.Check

data T : Set where A B C : T
data E : Set where e1 e2 e3 e4 : E
data P : Set where p0 : P
data K : Set where c0 : K
data Ru : Set where ρ₀ ρ₁ : Ru

tyEqT : (X Y : T) → Dec (X ≡ Y)
tyEqT A A = yes refl
tyEqT A B = no (λ ())
tyEqT A C = no (λ ())
tyEqT B A = no (λ ())
tyEqT B B = yes refl
tyEqT B C = no (λ ())
tyEqT C A = no (λ ())
tyEqT C B = no (λ ())
tyEqT C C = yes refl

tyEqT-refl : ∀ X → tyEqT X X ≡ yes refl
tyEqT-refl A = refl
tyEqT-refl B = refl
tyEqT-refl C = refl

G : Graph
G = record
  { Ty     = T
  ; EdgeId = E
  ; src    = λ { e1 → A ; e2 → B ; e3 → A ; e4 → A }
  ; tgt    = λ { e1 → B ; e2 → C ; e3 → C ; e4 → C }
  }

L : Lexicon
L = record
  { graph         = G
  ; tyEq          = tyEqT
  ; tyEq-refl     = tyEqT-refl
  ; PredId        = P
  ; ConstId       = K
  ; psig          = λ { p0 → [] }
  ; cty           = λ { c0 → A }
  ; edgeOf        = λ { zero → just e1 ; (suc zero) → just e2 ; (suc (suc zero)) → just e3 ; (suc (suc (suc zero))) → just e4 ; (suc (suc (suc (suc _)))) → nothing }
  ; edgeName      = λ { e1 → 0 ; e2 → 1 ; e3 → 2 ; e4 → 3 }
  ; edgeOf-name   = λ { e1 → refl ; e2 → refl ; e3 → refl ; e4 → refl }
  ; edgeOf-sound  = λ { zero e1 _ → refl ; zero e2 () ; zero e3 () ; zero e4 ()
                      ; (suc zero) e1 () ; (suc zero) e2 _ → refl ; (suc zero) e3 () ; (suc zero) e4 ()
                      ; (suc (suc zero)) e1 () ; (suc (suc zero)) e2 () ; (suc (suc zero)) e3 _ → refl ; (suc (suc zero)) e4 ()
                      ; (suc (suc (suc zero))) e1 () ; (suc (suc (suc zero))) e2 () ; (suc (suc (suc zero))) e3 () ; (suc (suc (suc zero))) e4 _ → refl
                      ; (suc (suc (suc (suc n)))) e1 () ; (suc (suc (suc (suc n)))) e2 () ; (suc (suc (suc (suc n)))) e3 () ; (suc (suc (suc (suc n)))) e4 () }
  ; predOf        = λ { zero → just p0 ; (suc _) → nothing }
  ; predName      = λ { p0 → 0 }
  ; predOf-name   = λ { p0 → refl }
  ; predOf-sound  = λ { zero p0 _ → refl ; (suc n) p0 () }
  ; constOf       = λ { zero → just c0 ; (suc _) → nothing }
  ; constName     = λ { c0 → 0 }
  ; constOf-name  = λ { c0 → refl }
  ; constOf-sound = λ { zero c0 _ → refl ; (suc n) c0 () }
  }

open Routes G

R : Rules G
R = record
  { RuleId = Ru
  ; rsrc   = λ { ρ₀ → A ; ρ₁ → A }
  ; rtgt   = λ { ρ₀ → C ; ρ₁ → C }
  ; lhs    = λ { ρ₀ → cons e1 (cons e2 nil) ; ρ₁ → cons e1 (cons e2 nil) }
  ; rhs    = λ { ρ₀ → cons e3 nil ; ρ₁ → cons e4 nil }
  }
