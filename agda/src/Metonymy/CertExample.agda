{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- End-to-end run of the extended certificate on a concrete knowledge-base snapshot.
-- Sentence: "Brussels rejected the proposal", with the place coerced to an institution.
-- Lexicon (Metonymy.ExampleKB): seat and gov are two coercions Place -> Inst; capital;govOf is equivalent
-- to gov. The snapshot has three places, three countries, four institutions and one proposal.
module Metonymy.CertExample where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Bool using (Bool ; true ; false)
import Cubical.Data.FinData as F
open import Cubical.Data.FinData using (Fin ; discreteFin)
open import Cubical.Data.List using (List ; [] ; _∷_ ; map)
open import Cubical.Data.List.Properties using (¬cons≡nil)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as E
open import Agda.Builtin.Maybe

open import Metonymy.ExampleKB
open import Metonymy.Check
open import Metonymy.Audit G R
open import Metonymy.Semantics G R using (SoundRules)
import Metonymy.Sentence L R as Sen
import Metonymy.Evidence L R as Ev
import Metonymy.FamilyCert L R ruleOfN as FC
import Metonymy.ThreeCert L R as TC
import Metonymy.Cert L R ruleOfN as Ct
import Metonymy.NormalizeFull L R as NF

------------------------------------------------------------------------------
-- The snapshot

sz : T → ℕ
sz Pl = 3        -- brussels, paris, rome
sz Co = 3        -- BE, FR, IT
sz In = 4        -- commission, belgovt, frgovt, itgovt
sz Pr = 1        -- the proposal

allFin : (n : ℕ) → List (Fin n)
allFin zero    = []
allFin (suc n) = F.zero ∷ map F.suc (allFin n)

private
  memMap : ∀ {n} {xs : List (Fin n)} {x : Fin n} → Mem x xs → Mem (F.suc x) (map F.suc xs)
  memMap here      = here
  memMap (there m) = there (memMap m)

allFin-complete : ∀ n (x : Fin n) → Mem x (allFin n)
allFin-complete zero    ()
allFin-complete (suc n) F.zero    = here
allFin-complete (suc n) (F.suc x) = there (memMap (allFin-complete n x))

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ (suc a) (suc b) = eqℕ a b
eqℕ _       _       = false

or : Bool → Bool → Bool
or true  _ = true
or false b = b

and : Bool → Bool → Bool
and true  b = b
and false _ = false

member : List (ℕ × ℕ) → ℕ → ℕ → Bool
member []             _ _ = false
member ((a , b) ∷ ps) x y = or (and (eqℕ a x) (eqℕ b y)) (member ps x y)

rel : E → List (ℕ × ℕ)
rel seat    = (0 , 0) ∷ []
rel gov     = (0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ []
rel capital = (0 , 0) ∷ (1 , 1) ∷ (2 , 2) ∷ []
rel govOf   = (0 , 1) ∷ (1 , 2) ∷ (2 , 3) ∷ []

fin : FinModel
fin = record
  { Elem           = λ A → Fin (sz A)
  ; elemEq         = λ A → discreteFin
  ; elems          = λ A → allFin (sz A)
  ; elems-complete = λ A x → allFin-complete (sz A) x
  ; tab            = λ e x y → member (rel e) (F.toℕ x) (F.toℕ y)
  }

-- Every declared equivalence holds in the snapshot (the audit runs by computation).
audit-ok : auditRule fin ρ₀ ≡ true
audit-ok = refl

sr : SoundRules (toModel fin)
sr = audit-all fin (λ { ρ₀ → audit-ok })

kb : Ev.KB
kb = record
  { fin      = fin
  ; refC     = λ { brussels → F.zero ; proposal → F.zero }
  ; predTab  = λ { reject (y , p , tt) → eqℕ (F.toℕ y) 0 ; active (y , tt) → true }
  ; unaryTab = λ { active In y → true ; _ _ _ → false }
  }

ne : ∀ ρ → NF.lhsN ρ ≡ [] → E.⊥
ne ρ₀ p = ¬cons≡nil p

module C = Ct.Cert kb sr ne

------------------------------------------------------------------------------
-- Reading the outcome of a check

tag : Maybe C.Checked → ℕ
tag nothing                = 0
tag (just (C.cResolve _))  = 1
tag (just (C.cRetain _))   = 2
tag (just (C.cFamily _))   = 3
tag (just (C.cConjoin _))  = 4
tag (just (C.cThree _))    = 5

------------------------------------------------------------------------------
-- 1. Resolve and Retain: reject(Brussels-as-institution, proposal)

-- seat coerces Brussels to the commission (index 0 of the institutions); the proposal is element 0.
sentence : RawCert
sentence = rawCert 0 (rawArg 0 (0 ∷ []) ∷ rawArg 1 [] ∷ [])

resolve-commission : tag (C.check (C.resolve (Ev.rawResolve sentence (0 ∷ 0 ∷ [])))) ≡ 1
resolve-commission = refl

retain-commission : tag (C.check (C.retain (Ev.rawResolve sentence (0 ∷ 0 ∷ [])))) ≡ 2
retain-commission = refl

-- The same referents are rejected when the route does not reach them: seat does not relate Brussels to belgovt.
resolve-wrong-referent : tag (C.check (C.resolve (Ev.rawResolve sentence (1 ∷ 0 ∷ [])))) ≡ 0
resolve-wrong-referent = refl

-- Reaching a referent along the route but failing the predicate is rejected too: take the gov coercion,
-- which reaches belgovt; reject(belgovt, proposal) is false in the snapshot.
sentence-gov : RawCert
sentence-gov = rawCert 0 (rawArg 0 (1 ∷ []) ∷ rawArg 1 [] ∷ [])

resolve-gov-false : tag (C.check (C.resolve (Ev.rawResolve sentence-gov (1 ∷ 0 ∷ [])))) ≡ 0
resolve-gov-false = refl

-- An ill-typed sentence (no coercion for the place) is rejected before any evidence is looked at.
resolve-no-coercion : tag (C.check (C.resolve (Ev.rawResolve (rawCert 0 (rawArg 0 [] ∷ rawArg 1 [] ∷ [])) (0 ∷ 0 ∷ [])))) ≡ 0
resolve-no-coercion = refl

------------------------------------------------------------------------------
-- 2. Family: the readings seat, gov and capital;govOf of the first argument of "reject"

-- Reading 0 = seat, reading 1 = gov, reading 2 = capital;govOf.
family-cert : FC.RawFamily
family-cert = FC.rawFamily 0 0 0
  ((0 ∷ []) ∷ (1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [])
  -- seat differs from gov and from capital;govOf (on Brussels and the commission)
  (FC.rawApart 0 1 0 0 ∷ FC.rawApart 0 2 0 0 ∷ [])
  -- gov and capital;govOf are the same reading: one rewriting step turns [capital, govOf] into [gov]
  (FC.rawSame 1 2 [] (FC.rawStep 0 [] [] ∷ []) ∷ [])

family-ok : tag (C.check (C.family family-cert)) ≡ 3
family-ok = refl

-- gov and capital;govOf cannot be apart: both relate Brussels to belgovt.
family-bad-apart : tag (C.check (C.family
  (FC.rawFamily 0 0 0 ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ []) (FC.rawApart 0 1 0 1 ∷ []) []))) ≡ 0
family-bad-apart = refl

-- A claimed equivalence without a valid chain of rewriting steps is rejected.
family-bad-same : tag (C.check (C.family
  (FC.rawFamily 0 0 0 ((0 ∷ []) ∷ (1 ∷ []) ∷ []) [] (FC.rawSame 0 1 [] [] ∷ [])))) ≡ 0
family-bad-same = refl

------------------------------------------------------------------------------
-- 3. Individuation: three places, each with its own government

triple123 : TC.Triple ℕ
triple123 = TC.triple 0 1 2

-- Under gov the three places (Brussels, Paris, Rome) reach three different institutions.
three-gov : TC.RawThree
three-gov = TC.rawThree 0 triple123
  (TC.rawConj (1 ∷ []) 1 (TC.triple 1 2 3) (TC.triple 1 1 2)) nothing

three-ok : tag (C.check (C.three three-gov)) ≡ 5
three-ok = refl

-- Copredication: also through capital;govOf. The images under both coercions differ.
three-copred : TC.RawThree
three-copred = TC.rawThree 0 triple123
  (TC.rawConj (1 ∷ []) 1 (TC.triple 1 2 3) (TC.triple 1 1 2))
  (just (TC.rawConj (2 ∷ 3 ∷ []) 1 (TC.triple 1 2 3) (TC.triple 1 1 2)))

three-copred-ok : tag (C.check (C.three three-copred)) ≡ 5
three-copred-ok = refl

-- The seat coercion relates only Brussels to anything, so witnesses claiming that Paris and Rome reach and
-- satisfy something under seat are rejected at the first satisfaction check.
three-seat : TC.RawThree
three-seat = TC.rawThree 0 triple123
  (TC.rawConj (0 ∷ []) 1 (TC.triple 0 0 0) (TC.triple 0 0 0)) nothing

three-seat-bad : tag (C.check (C.three three-seat)) ≡ 0
three-seat-bad = refl

------------------------------------------------------------------------------
-- 4. Conjoin: two coercions of the referent of "Brussels" at once

conjoin-ok : tag (C.check (C.conjoin (Ct.rawConjoin 0
  (TC.rawConj (0 ∷ []) 1 (TC.triple 0 0 0) (TC.triple 0 0 0))
  (TC.rawConj (1 ∷ []) 1 (TC.triple 1 0 0) (TC.triple 0 0 0))))) ≡ 4
conjoin-ok = refl

-- Correct satisfaction witnesses but a distinguishing referent that does not distinguish: under gov, Paris
-- and Rome both fail to reach belgovt (referent 1), so the pair (Paris, Rome) is not distinguished by it.
three-bad-dist : tag (C.check (C.three (TC.rawThree 0 triple123
  (TC.rawConj (1 ∷ []) 1 (TC.triple 1 2 3) (TC.triple 1 1 1)) nothing))) ≡ 0
three-bad-dist = refl

------------------------------------------------------------------------------
-- 5. A batch of certificates is accepted as a whole, by computation

batch-ok : C.acceptAll
  ( C.resolve (Ev.rawResolve sentence (0 ∷ 0 ∷ []))
  ∷ C.retain  (Ev.rawResolve sentence (0 ∷ 0 ∷ []))
  ∷ C.family family-cert
  ∷ C.three three-gov
  ∷ C.three three-copred
  ∷ [] ) ≡ true
batch-ok = refl

-- One bad certificate makes the batch fail.
batch-bad : C.acceptAll
  ( C.resolve (Ev.rawResolve sentence (0 ∷ 0 ∷ []))
  ∷ C.resolve (Ev.rawResolve sentence (1 ∷ 0 ∷ []))
  ∷ [] ) ≡ false
batch-bad = refl
