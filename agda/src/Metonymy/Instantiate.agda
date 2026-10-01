{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- Non-vacuity checks. The parameterized modules are instantiated on a concrete lexicon, the typed normalizer
-- is run (not just typechecked), and the finite-model audit validates the declared equivalence.
module Metonymy.Instantiate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as E
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool ; true ; false ; _≟_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Relation.Nullary using (Dec ; yes ; no)
open import Agda.Builtin.Maybe

open import Metonymy.ExampleRules
open import Metonymy.Graph
open import Metonymy.Check
open import Metonymy.NormalizeExample using (rules ; rules-complete ; sh ; cps ; module B)
open import Metonymy.Equivalence G R using (decEquiv ; classification)
open Routes G

-- The parameterized development applies to the example lexicon.
import Metonymy.Sentence L R as Sen
import Metonymy.Implicit L R as Imp
import Metonymy.Enumerate L as Enum
import Metonymy.Classify L R as Cls
import Metonymy.Coherence G R as Coh
import Metonymy.Context G R as Ctx
import Metonymy.Category G R as Cat
import Metonymy.Modes G R as Mod

------------------------------------------------------------------------------
-- The typed normalizer decides equivalence of routes, by computation

IsYes : ∀ {X : Type} → Dec X → Type
IsYes (yes _) = Unit
IsYes (no  _) = E.⊥

direct composite : Route A C
direct    = cons e3 nil
composite = cons e1 (cons e2 nil)

-- e1;e2 and e3 are equivalent, and the decision procedure finds it.
composite≈direct : IsYes (decEquiv B.normalizer composite direct)
composite≈direct = tt

-- A route is equivalent to itself.
direct≈direct : IsYes (decEquiv B.normalizer direct direct)
direct≈direct = tt
