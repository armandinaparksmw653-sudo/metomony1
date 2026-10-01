{-# OPTIONS --safe --cubical --guardedness #-}

-- Lexicon audit on a concrete finite model: the composite route e1;e2 is declared equivalent to the
-- direct edge e3. The audit accepts the correct table and rejects a wrong one, by computation.
module Metonymy.AuditExample where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; true ; false ; _≟_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete)

open import Metonymy.Graph

data T : Type where A B C : T
data E : Type where e1 e2 e3 : E
data Ru : Type where ρ₀ : Ru

G : Graph
G = record
  { Ty     = T
  ; EdgeId = E
  ; src    = λ { e1 → A ; e2 → B ; e3 → A }
  ; tgt    = λ { e1 → B ; e2 → C ; e3 → C }
  }

open Routes G

R : Rules G
R = record
  { RuleId = Ru
  ; rsrc   = λ { ρ₀ → A }
  ; rtgt   = λ { ρ₀ → C }
  ; lhs    = λ { ρ₀ → cons e1 (cons e2 nil) }
  ; rhs    = λ { ρ₀ → cons e3 nil }
  }

open import Metonymy.Audit G R
open import Metonymy.Semantics G R using (SoundRules)

-- Every sense type has two referents; carriers are enumerated.
bothBool : List Bool
bothBool = true ∷ false ∷ []

complete : ∀ (x : Bool) → Mem x bothBool
complete true  = here
complete false = there here

-- Edges relate a referent to itself (the intended, consistent tables).
idTab : Bool → Bool → Bool
idTab x y = decB' (x ≟ y)
  where
    decB' : ∀ {X : Type} → Dec X → Bool
    decB' (yes _) = true
    decB' (no _)  = false

good : FinModel
good = record
  { Elem           = λ _ → Bool
  ; elemEq         = λ _ → _≟_
  ; elems          = λ _ → bothBool
  ; elems-complete = λ _ → complete
  ; tab            = λ _ → idTab
  }

-- A wrong table: the direct edge e3 relates nothing, so e1;e2 and e3 are not equivalent.
bad : FinModel
bad = record
  { Elem           = λ _ → Bool
  ; elemEq         = λ _ → _≟_
  ; elems          = λ _ → bothBool
  ; elems-complete = λ _ → complete
  ; tab            = λ { e1 → idTab ; e2 → idTab ; e3 → λ _ _ → false }
  }

good-passes : auditRule good ρ₀ ≡ true
good-passes = refl

bad-fails : auditRule bad ρ₀ ≡ false
bad-fails = refl

-- And the audit result is a proof: in the good model the declared equivalence is semantically valid.
good-sound : SoundRules (toModel good)
good-sound = audit-all good (λ { ρ₀ → good-passes })
