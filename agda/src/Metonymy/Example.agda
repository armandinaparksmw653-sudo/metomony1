{-# OPTIONS --safe --cubical-compatible #-}

-- A concrete toy lexicon and certificates checked by computation.
-- Sentence: "Brussels rejected the proposal." (place-for-institution)
module Metonymy.Example where

open import Metonymy.Base
open import Metonymy.Graph
open import Metonymy.Check

data T : Set where
  place inst prop : T

data E : Set where
  placeForInst : E

data P : Set where
  reject : P

data C : Set where
  brussels proposal : C

tyEqT : (A B : T) → Dec (A ≡ B)
tyEqT place place = yes refl
tyEqT place inst  = no (λ ())
tyEqT place prop  = no (λ ())
tyEqT inst  place = no (λ ())
tyEqT inst  inst  = yes refl
tyEqT inst  prop  = no (λ ())
tyEqT prop  place = no (λ ())
tyEqT prop  inst  = no (λ ())
tyEqT prop  prop  = yes refl

tyEqT-refl : ∀ A → tyEqT A A ≡ yes refl
tyEqT-refl place = refl
tyEqT-refl inst  = refl
tyEqT-refl prop  = refl

G : Graph
G = record
  { Ty     = T
  ; EdgeId = E
  ; src    = λ { placeForInst → place }
  ; tgt    = λ { placeForInst → inst }
  }

L : Lexicon
L = record
  { graph         = G
  ; tyEq          = tyEqT
  ; tyEq-refl     = tyEqT-refl
  ; PredId        = P
  ; ConstId       = C
  ; psig          = λ { reject → inst ∷ prop ∷ [] }
  ; cty           = λ { brussels → place ; proposal → prop }
  ; edgeOf        = λ { zero → just placeForInst ; (suc _) → nothing }
  ; edgeName      = λ { placeForInst → 0 }
  ; edgeOf-name   = λ { placeForInst → refl }
  ; edgeOf-sound  = λ { zero placeForInst _ → refl ; (suc n) placeForInst () }
  ; predOf        = λ { zero → just reject ; (suc _) → nothing }
  ; predName      = λ { reject → 0 }
  ; predOf-name   = λ { reject → refl }
  ; predOf-sound  = λ { zero reject _ → refl ; (suc n) reject () }
  ; constOf       = λ { zero → just brussels ; (suc zero) → just proposal ; (suc (suc _)) → nothing }
  ; constName     = λ { brussels → 0 ; proposal → 1 }
  ; constOf-name  = λ { brussels → refl ; proposal → refl }
  ; constOf-sound = λ { zero brussels _ → refl
                      ; zero proposal ()
                      ; (suc zero) brussels ()
                      ; (suc zero) proposal _ → refl
                      ; (suc (suc n)) brussels ()
                      ; (suc (suc n)) proposal () }
  }

open Checker L
open Routes G

-- reject(Brussels -[placeForInst]-> Institution, proposal)
good : RawCert
good = rawCert 0 (rawArg 0 (0 ∷ []) ∷ rawArg 1 [] ∷ [])

good-accepted : checkCert good ≡ just (pred reject (acons (ent brussels (cons placeForInst nil))
                                                          (acons (ent proposal nil) anil)))
good-accepted = refl

-- Missing coercion: Place does not fit the Institution slot.
no-coercion : RawCert
no-coercion = rawCert 0 (rawArg 0 [] ∷ rawArg 1 [] ∷ [])

no-coercion-rejected : checkCert no-coercion ≡ nothing
no-coercion-rejected = refl

-- Unknown edge identifier.
bad-edge : RawCert
bad-edge = rawCert 0 (rawArg 0 (7 ∷ []) ∷ rawArg 1 [] ∷ [])

bad-edge-rejected : checkCert bad-edge ≡ nothing
bad-edge-rejected = refl

-- Wrong arity.
bad-arity : RawCert
bad-arity = rawCert 0 (rawArg 0 (0 ∷ []) ∷ [])

bad-arity-rejected : checkCert bad-arity ≡ nothing
bad-arity-rejected = refl
