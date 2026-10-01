{-# OPTIONS --safe --cubical --guardedness #-}
module Everything where

open import Metonymy.Base
open import Metonymy.Graph
open import Metonymy.Check
open import Metonymy.Example
open import Metonymy.Semantics
open import Metonymy.Counting
open import Metonymy.Modes
open import Metonymy.Equivalence
open import Metonymy.Context
open import Metonymy.Reencode
open import Metonymy.Category
open import Metonymy.Audit
open import Metonymy.AuditExample
open import Metonymy.Image
open import Metonymy.Quantified

-- Modules parameterized by a lexicon or a graph are imported without arguments (they are still checked).
import Metonymy.Sentence
import Metonymy.QuantifiedRoutes
import Metonymy.Implicit
import Metonymy.ReencodeUA
import Metonymy.Enumerate
import Metonymy.Classify
import Metonymy.Rewriting
import Metonymy.Normalize
import Metonymy.TypedFactor
import Metonymy.StringRewriting
import Metonymy.NormalizeFull

-- Concrete lexicons with declared equivalences: the complete normalizer, and a rejected non-confluent system.
open import Metonymy.ExampleRules
open import Metonymy.ExampleRulesBad
open import Metonymy.NormalizeExample
open import Metonymy.NormalizeExampleBad
