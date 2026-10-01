{-# OPTIONS --safe --cubical --guardedness -WnoUnsupportedIndexedMatch #-}

-- The extended certificate. A raw certificate now carries a mode and the evidence for it:
--   resolve  : the coerced sentence and the chosen referents; the checker proves the referents satisfy it;
--   retain   : the same data, but the claim is only the truncated existence of satisfying referents;
--   family   : candidate readings, pairs proved different (apartness witnesses) and pairs proved the same
--              (rewriting chains): a proved partial description of the set of readings;
--   conjoin  : two coercions of one referent, each with a witness: the conjunction of two Retain claims;
--   three    : individuation: three referents, pairwise distinguished under every coercion used.
-- `check` turns a raw certificate into a Checked value, and `meaning` states what each Checked value
-- establishes in the knowledge-base snapshot. Nothing is assumed about the producer of the raw certificate.
open import Agda.Builtin.Maybe
open import Cubical.Data.Nat using (ℕ)
open import Metonymy.Graph
open import Metonymy.Check

module Metonymy.Cert
  (L : Lexicon) (R : Rules (Lexicon.graph L))
  (ruleOf : ℕ → Maybe (Rules.RuleId R))
  where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Bool using (Bool ; true ; false ; _and_)
open import Cubical.Data.List using (List ; [] ; _∷_)
import Cubical.Data.Empty as E
open import Cubical.Functions.Logic
open import Cubical.HITs.SetQuotients using ([_])

open Lexicon L
open Routes graph using (Route)
open Checker L
open import Metonymy.Audit graph R using (FinModel ; toModel)
open import Metonymy.Semantics graph R using (Model ; SoundRules ; Coe)
open import Metonymy.Modes graph R using (Conjoin)
import Metonymy.Sentence L R as Sen
open import Metonymy.Evidence L R as Ev using (KB ; bindM ; nth)
import Metonymy.FamilyCert L R ruleOf as FC
import Metonymy.ThreeCert L R as TC
open import Metonymy.Quantified using (Three₁ ; Three₂)
open import Metonymy.NormalizeFull L R using (lhsN)

record RawConjoin : Type where
  constructor rawConjoin
  field
    cname : ℕ                -- a constant: the referent being coerced in two ways
    conj1 : TC.RawConj       -- only the first satisfaction witness is used
    conj2 : TC.RawConj

module Cert (K : KB) (sr : SoundRules (toModel (KB.fin K))) (ne : ∀ ρ → lhsN ρ ≡ [] → E.⊥) where
  open KB K
  module TCK = TC.Check K

  data Raw : Type where
    resolve : Ev.RawResolve K → Raw
    retain  : Ev.RawResolve K → Raw
    family  : FC.RawFamily → Raw
    conjoin : RawConjoin → Raw
    three   : TC.RawThree → Raw

  -- Conjoin: two coercions of the referent of a constant, each with a satisfying witness.
  record ConjoinOK : Type₁ where
    field
      X B C : Ty
      x     : FinModel.Elem fin X
      r     : Route X B
      P     : PredId
      s     : Route X C
      Q     : PredId
      holds : ⟨ Conjoin (toModel fin) r (TC.Check.Rel.pr K r P) s (TC.Check.Rel.pr K s Q) x ⟩

  checkConjoin : RawConjoin → Maybe ConjoinOK
  checkConjoin (rawConjoin cn (TC.rawConj rn1 pn1 (TC.triple a1 _ _) _) (TC.rawConj rn2 pn2 (TC.triple a2 _ _) _)) =
    bindM (constOf cn) (λ c →
    bindM (predOf pn1) (λ P →
    bindM (nth (psig P) 0) (λ B →
    bindM (checkRoute (cty c) B rn1) (λ r →
    bindM (TC.Check.Rel.checkSat K r P (refC c) a1) (λ s1 →
    bindM (predOf pn2) (λ Q →
    bindM (nth (psig Q) 0) (λ C →
    bindM (checkRoute (cty c) C rn2) (λ s →
    bindM (TC.Check.Rel.checkSat K s Q (refC c) a2) (λ s2 →
    just (record { X = cty c ; B = B ; C = C ; x = refC c ; r = r ; P = P ; s = s ; Q = Q
                 ; holds = s1 , s2 }))))))))))

  -- What a passed check carries.
  data Checked : Type₁ where
    cResolve : ∀ {c} → Ev.Resolved K c → Checked
    cRetain  : ∀ {c} → Ev.Resolved K c → Checked
    cFamily  : FC.FamilyOK → Checked
    cConjoin : ConjoinOK → Checked
    cThree   : TCK.ThreeOK → Checked

  check : Raw → Maybe Checked
  check (resolve raw) = bindM (Ev.checkResolve K raw) (λ r → just (cResolve r))
  check (retain raw)  = bindM (Ev.checkResolve K raw) (λ r → just (cRetain r))
  check (family raw)  = bindM (FC.Check.checkFamily K sr ne raw) (λ f → just (cFamily f))
  check (conjoin raw) = bindM (checkConjoin raw) (λ j → just (cConjoin j))
  check (three raw)   = bindM (TC.Check.checkThree K raw) (λ t → just (cThree t))

  -- The statement about a claim of a family of readings.
  ClaimHolds : ∀ {A B} → FC.Claim A B → Type
  ClaimHolds {A} {B} (FC.distinct r s _) = Path (Coe A B) [ r ] [ s ] → E.⊥
  ClaimHolds {A} {B} (FC.equal r s _)    = Path (Coe A B) [ r ] [ s ]

  AllHold : ∀ {A B} → List (FC.Claim A B) → Type
  AllHold []       = Unit
  AllHold (c ∷ cs) = ClaimHolds c × AllHold cs

  allHold : ∀ {A B} (cs : List (FC.Claim A B)) → AllHold cs
  allHold []                      = tt
  allHold (FC.distinct r s d ∷ cs) = d , allHold cs
  allHold (FC.equal r s e ∷ cs)    = e , allHold cs

  -- What each kind of checked certificate establishes in the snapshot's model.
  -- (Lift places statements living in Type into Type1 so that one function can describe all modes.)
  Meaning : Checked → Type₁
  Meaning (cResolve {c} r) = Lift {ℓ-zero} {ℓ-suc ℓ-zero} (Ev.ResolveHolds K (Ev.Resolved.form r) (Ev.Resolved.ys r))
  Meaning (cRetain  {c} r) = Lift {ℓ-zero} {ℓ-suc ℓ-zero} ⟨ Sen.formSem (Ev.smodel K) (Ev.Resolved.form r) ⟩
  Meaning (cFamily ok)     = Lift {ℓ-zero} {ℓ-suc ℓ-zero} (AllHold (FC.FamilyOK.claims ok))
  Meaning (cConjoin j)     =
    Lift {ℓ-zero} {ℓ-suc ℓ-zero}
      ⟨ Conjoin (toModel fin) (ConjoinOK.r j) (TC.Check.Rel.pr K (ConjoinOK.r j) (ConjoinOK.P j))
                              (ConjoinOK.s j) (TC.Check.Rel.pr K (ConjoinOK.s j) (ConjoinOK.Q j)) (ConjoinOK.x j) ⟩
  Meaning (cThree (TCK.one r P h))     = Three₁ (TC.Check.Rel.ρ K r P) (TC.Check.Rel.pr K r P)
  Meaning (cThree (TCK.two r P s Q h)) =
    Three₂ (TC.Check.Rel.ρ K r P) (TC.Check.Rel.pr K r P) (TC.Check.Rel.ρ K s Q) (TC.Check.Rel.pr K s Q)

  -- Soundness of the checker: every accepted certificate establishes its meaning.
  meaning : (ck : Checked) → Meaning ck
  meaning (cResolve r) = lift (Ev.Resolved.holds r)
  meaning (cRetain  r) = lift (Ev.retained K r)
  meaning (cFamily ok) = lift (allHold (FC.FamilyOK.claims ok))
  meaning (cConjoin j) = lift (ConjoinOK.holds j)
  meaning (cThree (TCK.one r P h))     = h
  meaning (cThree (TCK.two r P s Q h)) = h

  -- Batch checking: a generated module lists the raw certificates of a corpus, and the proof that the
  -- whole batch is accepted is a computation (`acceptAll batch ≡ true` by refl).
  accepted : Maybe Checked → Bool
  accepted nothing  = false
  accepted (just _) = true

  acceptAll : List Raw → Bool
  acceptAll []       = true
  acceptAll (r ∷ rs) = accepted (check r) and acceptAll rs
