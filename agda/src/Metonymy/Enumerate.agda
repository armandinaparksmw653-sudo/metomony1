{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- T7' and decidable equality of routes.
--   * Routes are determined by the names of their edges (the checker is a retraction), so equality of
--     routes is decidable.
--   * Every route up to a length bound occurs in the enumerated list of routes (completeness relative
--     to the lexicon and the bound).
--   * A covering-and-apartness certificate pins down the number of readings up to the bound.
open import Agda.Builtin.Maybe
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Enumerate (L : Lexicon) where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; discreteℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as E
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; map)
open import Cubical.Data.List.Properties using (discreteList)
open import Cubical.Relation.Nullary using (Dec ; yes ; no ; Discrete)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁ ; ∣_∣₁ ; isPropPropTrunc)
import Agda.Builtin.Equality as B

open Lexicon L
open Routes graph using (Route ; nil ; cons)
open Checker L

private
  toPath : ∀ {ℓ} {X : Type ℓ} {x y : X} → x B.≡ y → x ≡ y
  toPath B.refl = refl

  fromJust : ∀ {X : Type} → X → Maybe X → X
  fromJust d nothing  = d
  fromJust d (just x) = x

------------------------------------------------------------------------------
-- Decidable equality of routes

routeNames-inj : ∀ {A B} {r s : Route A B} → routeNames r ≡ routeNames s → r ≡ s
routeNames-inj {A} {B} {r} {s} p =
  cong (fromJust r) (sym (toPath (checkRoute-complete r)) ∙ cong (checkRoute A B) p ∙ toPath (checkRoute-complete s))

routeEq : ∀ {A B} → Discrete (Route A B)
routeEq r s with discreteList discreteℕ (routeNames r) (routeNames s)
... | yes p  = yes (routeNames-inj p)
... | no  ¬p = no (λ q → ¬p (cong routeNames q))

------------------------------------------------------------------------------
-- Finite lists: membership and the list operations used for enumeration

data Mem {X : Type} (x : X) : List X → Type where
  here  : ∀ {xs} → Mem x (x ∷ xs)
  there : ∀ {y xs} → Mem x xs → Mem x (y ∷ xs)

Mem-++ˡ : ∀ {X : Type} {x : X} {xs : List X} (ys : List X) → Mem x xs → Mem x (xs ++ ys)
Mem-++ˡ ys here      = here
Mem-++ˡ ys (there m) = there (Mem-++ˡ ys m)

Mem-++ʳ : ∀ {X : Type} {x : X} (xs : List X) {ys : List X} → Mem x ys → Mem x (xs ++ ys)
Mem-++ʳ []       m = m
Mem-++ʳ (z ∷ xs) m = there (Mem-++ʳ xs m)

Mem-map : ∀ {X Y : Type} (g : X → Y) {x : X} {xs : List X} → Mem x xs → Mem (g x) (map g xs)
Mem-map g here      = here
Mem-map g (there m) = there (Mem-map g m)

concatMap : ∀ {X Y : Type} → (X → List Y) → List X → List Y
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

Mem-concatMap : ∀ {X Y : Type} (f : X → List Y) {a : X} {as : List X} {y : Y}
              → Mem a as → Mem y (f a) → Mem y (concatMap f as)
Mem-concatMap f {as = a ∷ as'} here      m = Mem-++ˡ (concatMap f as') m
Mem-concatMap f {as = b ∷ as'} (there h) m = Mem-++ʳ (f b) (Mem-concatMap f h m)

consMaybe : ∀ {Y : Type} → Maybe Y → List Y → List Y
consMaybe nothing  ys = ys
consMaybe (just y) ys = y ∷ ys

filterMap : ∀ {X Y : Type} → (X → Maybe Y) → List X → List Y
filterMap f []       = []
filterMap f (x ∷ xs) = consMaybe (f x) (filterMap f xs)

Mem-consMaybe-there : ∀ {Y : Type} {y : Y} (m : Maybe Y) {ys : List Y} → Mem y ys → Mem y (consMaybe m ys)
Mem-consMaybe-there nothing  h = h
Mem-consMaybe-there (just z) h = there h

Mem-filterMap : ∀ {X Y : Type} (f : X → Maybe Y) {x : X} {xs : List X} {y : Y}
              → Mem x xs → f x ≡ just y → Mem y (filterMap f xs)
Mem-filterMap f {x} {xs = x ∷ xs'} {y} here p = subst (λ m → Mem y (consMaybe m (filterMap f xs'))) (sym p) here
Mem-filterMap f {xs = z ∷ xs'} (there h) p = Mem-consMaybe-there (f z) (Mem-filterMap f h p)

------------------------------------------------------------------------------
-- Enumeration of routes up to a length bound

-- All lists over an alphabet of identifiers with at most k elements.
listsUpTo : ℕ → List ℕ → List (List ℕ)
listsUpTo zero    alph = [] ∷ []
listsUpTo (suc k) alph = [] ∷ concatMap (λ a → map (λ l → a ∷ l) (listsUpTo k alph)) alph

-- A route fits within k edges.
Fuel : ∀ {A B} → Route A B → ℕ → Type
Fuel nil        k       = Unit
Fuel (cons e r) zero    = E.⊥
Fuel (cons e r) (suc k) = Fuel r k

-- Names of edges, as an alphabet that mentions every edge.
Alphabet : List ℕ → Type
Alphabet alph = ∀ e → Mem (edgeName e) alph

names-listed : ∀ {A B} (r : Route A B) (k : ℕ) (alph : List ℕ) → Alphabet alph → Fuel r k
             → Mem (routeNames r) (listsUpTo k alph)
names-listed nil zero    alph al _ = here
names-listed nil (suc k) alph al _ = here
names-listed (cons e r) zero    alph al ()
names-listed (cons e r) (suc k) alph al f =
  there (Mem-concatMap (λ a → map (λ l → a ∷ l) (listsUpTo k alph)) (al e)
           (Mem-map (λ l → edgeName e ∷ l) (names-listed r k alph al f)))

-- The enumerated routes from A to B.
routesUpTo : ℕ → List ℕ → (A B : Ty) → List (Route A B)
routesUpTo k alph A B = filterMap (checkRoute A B) (listsUpTo k alph)

-- T7'. Every route within the bound occurs in the enumeration.
routesUpTo-complete : ∀ {A B} (r : Route A B) (k : ℕ) (alph : List ℕ) → Alphabet alph → Fuel r k
                    → Mem r (routesUpTo k alph A B)
routesUpTo-complete r k alph al f =
  Mem-filterMap (checkRoute _ _) (names-listed r k alph al f) (toPath (checkRoute-complete r))
