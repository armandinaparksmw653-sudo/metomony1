{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Negative test: the critical-pair checker rejects a non-confluent rule system.
module Metonymy.NormalizeExampleBad where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Agda.Builtin.Maybe

open import Metonymy.ExampleRulesBad
open import Metonymy.Check
import Metonymy.NormalizeFull L R as NF

module S = NF.S

rules : List Ru
rules = ρ₀ ∷ ρ₁ ∷ []

rules-complete : ∀ ρ → S.Mem ρ rules
rules-complete ρ₀ = S.here
rules-complete ρ₁ = S.there S.here

module Chk = S.Checker rules rules-complete 20

-- The two rules share a left-hand side but have different right-hand sides that cannot be joined:
-- the check fails.
rejected : Chk.check1 ≡ nothing
rejected = refl
