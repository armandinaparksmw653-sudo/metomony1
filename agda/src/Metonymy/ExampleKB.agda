{-# OPTIONS --safe --cubical-compatible #-}

-- A lexicon with ambiguous place-for-institution coercions and one declared equivalence:
--   seat : Place -> Inst        (EU institutions seated in the place)
--   gov  : Place -> Inst        (the government of the place's country)
--   capital;govOf is equivalent to gov.
module Metonymy.ExampleKB where

open import Metonymy.Base
open import Metonymy.Graph
open import Metonymy.Check

data T : Set where Pl Co In Pr : T
data E : Set where seat gov capital govOf : E
data P : Set where reject active : P
data K : Set where brussels proposal : K
data Ru : Set where ρ₀ : Ru

tyEqT : (X Y : T) → Dec (X ≡ Y)
tyEqT Pl Pl = yes refl
tyEqT Pl Co = no (λ ())
tyEqT Pl In = no (λ ())
tyEqT Pl Pr = no (λ ())
tyEqT Co Pl = no (λ ())
tyEqT Co Co = yes refl
tyEqT Co In = no (λ ())
tyEqT Co Pr = no (λ ())
tyEqT In Pl = no (λ ())
tyEqT In Co = no (λ ())
tyEqT In In = yes refl
tyEqT In Pr = no (λ ())
tyEqT Pr Pl = no (λ ())
tyEqT Pr Co = no (λ ())
tyEqT Pr In = no (λ ())
tyEqT Pr Pr = yes refl

tyEqT-refl : ∀ X → tyEqT X X ≡ yes refl
tyEqT-refl Pl = refl
tyEqT-refl Co = refl
tyEqT-refl In = refl
tyEqT-refl Pr = refl

G : Graph
G = record
  { Ty     = T
  ; EdgeId = E
  ; src    = λ { seat → Pl; gov → Pl; capital → Pl; govOf → Co }
  ; tgt    = λ { seat → In; gov → In; capital → Co; govOf → In }
  }

L : Lexicon
L = record
  { graph         = G
  ; tyEq          = tyEqT
  ; tyEq-refl     = tyEqT-refl
  ; PredId        = P
  ; ConstId       = K
  ; psig          = λ { reject → In ∷ Pr ∷ []; active → In ∷ [] }
  ; cty           = λ { brussels → Pl; proposal → Pr }
  ; edgeOf        = λ { zero → just seat; (suc zero) → just gov; (suc (suc zero)) → just capital; (suc (suc (suc zero))) → just govOf; (suc (suc (suc (suc _)))) → nothing }
  ; edgeName      = λ { seat → 0; gov → 1; capital → 2; govOf → 3 }
  ; edgeOf-name   = λ { seat → refl; gov → refl; capital → refl; govOf → refl }
  ; edgeOf-sound  = λ { zero seat _ → refl
                      ; zero gov ()
                      ; zero capital ()
                      ; zero govOf ()
                      ; (suc zero) seat ()
                      ; (suc zero) gov _ → refl
                      ; (suc zero) capital ()
                      ; (suc zero) govOf ()
                      ; (suc (suc zero)) seat ()
                      ; (suc (suc zero)) gov ()
                      ; (suc (suc zero)) capital _ → refl
                      ; (suc (suc zero)) govOf ()
                      ; (suc (suc (suc zero))) seat ()
                      ; (suc (suc (suc zero))) gov ()
                      ; (suc (suc (suc zero))) capital ()
                      ; (suc (suc (suc zero))) govOf _ → refl
                      ; (suc (suc (suc (suc n)))) seat ()
                      ; (suc (suc (suc (suc n)))) gov ()
                      ; (suc (suc (suc (suc n)))) capital ()
                      ; (suc (suc (suc (suc n)))) govOf () }
  ; predOf        = λ { zero → just reject; (suc zero) → just active; (suc (suc _)) → nothing }
  ; predName      = λ { reject → 0; active → 1 }
  ; predOf-name   = λ { reject → refl; active → refl }
  ; predOf-sound  = λ { zero reject _ → refl
                      ; zero active ()
                      ; (suc zero) reject ()
                      ; (suc zero) active _ → refl
                      ; (suc (suc n)) reject ()
                      ; (suc (suc n)) active () }
  ; constOf       = λ { zero → just brussels; (suc zero) → just proposal; (suc (suc _)) → nothing }
  ; constName     = λ { brussels → 0; proposal → 1 }
  ; constOf-name  = λ { brussels → refl; proposal → refl }
  ; constOf-sound = λ { zero brussels _ → refl
                      ; zero proposal ()
                      ; (suc zero) brussels ()
                      ; (suc zero) proposal _ → refl
                      ; (suc (suc n)) brussels ()
                      ; (suc (suc n)) proposal () }
  }

open Routes G

-- capital;govOf is equivalent to gov.
R : Rules G
R = record
  { RuleId = Ru
  ; rsrc   = λ { ρ₀ → Pl }
  ; rtgt   = λ { ρ₀ → In }
  ; lhs    = λ { ρ₀ → cons capital (cons govOf nil) }
  ; rhs    = λ { ρ₀ → cons gov nil }
  }

-- Raw name resolution for rules (identifier 0 is the only rule).
ruleOfN : ℕ → Maybe Ru
ruleOfN zero = just ρ₀
ruleOfN (suc _) = nothing
