{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- The complete normalizer on a concrete lexicon. The critical-pair conditions are not assumed: they are
-- established by running the checker, and the normal form of a route is computed.
module Metonymy.NormalizeExample where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.List using (List ; [] ; _∷_ ; length)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as E
open import Cubical.Data.Sigma
open import Agda.Builtin.Maybe

open import Metonymy.ExampleRules
open import Metonymy.Check
import Metonymy.NormalizeFull L R as NF

module S = NF.S

rules : List Ru
rules = ρ₀ ∷ []

rules-complete : ∀ ρ → S.Mem ρ rules
rules-complete ρ₀ = S.here

-- Every rule shortens the route: 1 < 2.
sh : S.Shrinks
sh ρ₀ = 0 , refl

private
  IsJust : ∀ {X : Type} → Maybe X → Type
  IsJust nothing  = E.⊥
  IsJust (just _) = Unit

  fromJust? : ∀ {X : Type} (m : Maybe X) → IsJust m → X
  fromJust? (just x) _ = x

module Chk = S.Checker rules rules-complete 20

-- The check runs and succeeds: the critical-pair conditions hold for this lexicon.
-- (If the check failed, `tt` below would not typecheck.)
cps : S.CP1 × S.CP2
cps = fromJust? Chk.cpDecide tt

-- The complete normalizer, with no assumptions left.
module B = NF.Build rules rules-complete sh (fst cps) (snd cps)

-- The normal form of the names [e1, e2] = [0, 1] is [e3] = [2].
normal-form : B.NN.normS (0 ∷ 1 ∷ []) ≡ 2 ∷ []
normal-form = refl

-- A route that does not contain the pattern is already normal.
already-normal : B.NN.normS (2 ∷ []) ≡ 2 ∷ []
already-normal = refl

-- The pattern inside a longer string is rewritten in context: [e1,e2] followed by nothing, preceded by e1? 
-- Here: e3 followed by the pattern is not a valid route, but the string rewriting itself is context-closed.
in-context : B.NN.normS (2 ∷ 0 ∷ 1 ∷ []) ≡ 2 ∷ 2 ∷ []
in-context = refl
