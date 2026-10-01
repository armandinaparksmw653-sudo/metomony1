{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- T7' (certificate form). A list of representative routes classifies all readings within a length bound
-- when (1) every enumerated route is equivalent to a representative and (2) distinct representatives are
-- apart in a model. Then the readings within the bound are exactly the classes of the representatives,
-- pairwise distinct, so their number is the length of the list.
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Classify (L : Lexicon) (R : Rules (Lexicon.graph L)) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Empty as E
open import Cubical.Data.List using (List)
open import Cubical.Relation.Nullary using (Dec ; yes ; no)
open import Cubical.HITs.SetQuotients as SQ using ([_] ; eq/)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)

open Lexicon L
open Routes graph using (Route)
open Equiv graph R
open import Metonymy.Enumerate L
open import Metonymy.Semantics graph R using (Model ; SoundRules ; Coe)
open import Metonymy.Equivalence graph R using (Apart ; apart⇒distinct)

-- The reading class of a route.
cls : ∀ {A B} → Route A B → Coe A B
cls r = [ r ]

module _ {A B : Ty} (k : ℕ) (alph : List ℕ) (al : Alphabet alph) (reps : List (Route A B)) where

  -- Every enumerated route is equivalent to some representative.
  Covers : Type
  Covers = ∀ r → Mem r (routesUpTo k alph A B) → ∥ Σ (Route A B) (λ s → Mem s reps × (r ≈ s)) ∥₁

  -- Every route within the bound is covered, hence every reading within the bound is a representative class.
  readings-covered : Covers → ∀ r → Fuel r k → ∥ Σ (Route A B) (λ s → Mem s reps × (cls r ≡ cls s)) ∥₁
  readings-covered cov r f =
    PT.rec isPropPropTrunc (λ { (s , m , h) → ∣ s , m , eq/ {R = _≈_} r s h ∣₁ }) (cov r (routesUpTo-complete r k alph al f))

  -- Representatives that are pairwise apart in a model are pairwise distinct readings.
  reps-distinct : ∀ (M : Model) (sr : SoundRules M)
                → (∀ s t → Mem s reps → Mem t reps → (s ≡ t → E.⊥) → Apart M sr s t)
                → ∀ s t → Mem s reps → Mem t reps → cls s ≡ cls t → s ≡ t
  reps-distinct M sr ap s t ms mt p with routeEq s t
  ... | yes q  = q
  ... | no  ¬q = E.rec (apart⇒distinct M sr (ap s t ms mt ¬q) p)
