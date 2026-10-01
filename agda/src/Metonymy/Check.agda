{-# OPTIONS --safe --cubical-compatible #-}

-- Syntactic layer: lexicon interface, typed sentences with explicit coercions (intrinsically typed),
-- raw certificates (identifiers only, as emitted by the Haskell core) and the certificate checker.
--   T1/T16: the checker is sound and complete, hence typing of certificates is decidable.
--   Surface preservation: inserting coercions never changes the underlying sentence.
module Metonymy.Check where

open import Metonymy.Base
open import Metonymy.Graph

-- What the checker needs from a lexicon. Name resolution is by natural-number identifiers;
-- the `*-sound` / `*-name` fields say that names and identifiers correspond.
record Lexicon : Set₁ where
  field
    graph : Graph
  open Graph graph public
  field
    tyEq      : (A B : Ty) → Dec (A ≡ B)
    tyEq-refl : ∀ A → tyEq A A ≡ yes refl

    PredId  : Set
    ConstId : Set
    psig    : PredId → List Ty      -- argument types of each predicate
    cty     : ConstId → Ty          -- literal (lexical) type of each constant

    edgeOf       : ℕ → Maybe EdgeId
    edgeName     : EdgeId → ℕ
    edgeOf-name  : ∀ e → edgeOf (edgeName e) ≡ just e
    edgeOf-sound : ∀ n e → edgeOf n ≡ just e → edgeName e ≡ n

    predOf       : ℕ → Maybe PredId
    predName     : PredId → ℕ
    predOf-name  : ∀ P → predOf (predName P) ≡ just P
    predOf-sound : ∀ n P → predOf n ≡ just P → predName P ≡ n

    constOf       : ℕ → Maybe ConstId
    constName     : ConstId → ℕ
    constOf-name  : ∀ c → constOf (constName c) ≡ just c
    constOf-sound : ∀ n c → constOf n ≡ just c → constName c ≡ n

-- Raw certificates: what crosses the Haskell -> Agda boundary.
record RawArg : Set where
  constructor rawArg
  field
    cname : ℕ
    route : List ℕ

record RawCert : Set where
  constructor rawCert
  field
    pname : ℕ
    args  : List RawArg

module Checker (L : Lexicon) where
  open Lexicon L
  open Routes graph

  ---------------------------------------------------------------------------
  -- Routes from edge names

  routeNames : ∀ {A B} → Route A B → List ℕ
  routeNames nil        = []
  routeNames (cons e r) = edgeName e ∷ routeNames r

  mutual
    checkRoute : (A B : Ty) → List ℕ → Maybe (Route A B)
    checkRoute A B []       = routeNil A B (tyEq A B)
    checkRoute A B (n ∷ ns) = stepE A B ns (edgeOf n)

    routeNil : (A B : Ty) → Dec (A ≡ B) → Maybe (Route A B)
    routeNil A .A (yes refl) = just nil
    routeNil A B  (no _)     = nothing

    stepE : (A B : Ty) → List ℕ → Maybe EdgeId → Maybe (Route A B)
    stepE A B ns nothing  = nothing
    stepE A B ns (just e) = stepT A B e ns (tyEq A (src e))

    stepT : (A B : Ty) (e : EdgeId) → List ℕ → Dec (A ≡ src e) → Maybe (Route A B)
    stepT A B e ns (no _)            = nothing
    stepT .(src e) B e ns (yes refl) = mapMaybe (cons e) (checkRoute (tgt e) B ns)

  mutual
    checkRoute-sound : ∀ A B ns {r : Route A B} → checkRoute A B ns ≡ just r → routeNames r ≡ ns
    checkRoute-sound A B []       eq = routeNil-sound A B (tyEq A B) eq
    checkRoute-sound A B (n ∷ ns) eq = stepE-sound A B n ns (edgeOf n) refl eq

    routeNil-sound : ∀ A B (d : Dec (A ≡ B)) {r : Route A B} → routeNil A B d ≡ just r → routeNames r ≡ []
    routeNil-sound A .A (yes refl) eq with just-inj eq
    ... | refl = refl
    routeNil-sound A B (no _) ()

    stepE-sound : ∀ A B n ns (m : Maybe EdgeId) {r : Route A B}
                → edgeOf n ≡ m → stepE A B ns m ≡ just r → routeNames r ≡ n ∷ ns
    stepE-sound A B n ns nothing  _   ()
    stepE-sound A B n ns (just e) eqE eq = stepT-sound A B n ns e (edgeOf-sound n e eqE) (tyEq A (src e)) eq

    stepT-sound : ∀ A B n ns (e : EdgeId) → edgeName e ≡ n → (d : Dec (A ≡ src e)) {r : Route A B}
                → stepT A B e ns d ≡ just r → routeNames r ≡ n ∷ ns
    stepT-sound A B n ns e en (no _) ()
    stepT-sound .(src e) B n ns e en (yes refl) eq with mapMaybe-just (cons e) (checkRoute (tgt e) B ns) eq
    ... | r' , eqR , refl = cong₂ _∷_ en (checkRoute-sound (tgt e) B ns eqR)

  checkRoute-complete : ∀ {A B} (r : Route A B) → checkRoute A B (routeNames r) ≡ just r
  checkRoute-complete {A} nil        = cong (routeNil A A) (tyEq-refl A)
  checkRoute-complete {B = B} (cons e r) =
    trans (cong (stepE (src e) B (routeNames r)) (edgeOf-name e))
      (trans (cong (stepT (src e) B e (routeNames r)) (tyEq-refl (src e)))
             (cong (mapMaybe (cons e)) (checkRoute-complete r)))

  ---------------------------------------------------------------------------
  -- Typed sentences with explicit coercions (intrinsically typed)

  -- An argument of type B: a constant together with an explicit coercion route from its literal type.
  data Ent (B : Ty) : Set where
    ent : (c : ConstId) → Route (cty c) B → Ent B

  data Args : List Ty → Set where
    anil  : Args []
    acons : ∀ {A As} → Ent A → Args As → Args (A ∷ As)

  data Form : Set where
    pred : (P : PredId) → Args (psig P) → Form

  -- Forgetting the typing: back to raw data.
  entRaw : ∀ {B} → Ent B → RawArg
  entRaw (ent c r) = rawArg (constName c) (routeNames r)

  argsRaw : ∀ {As} → Args As → List RawArg
  argsRaw anil         = []
  argsRaw (acons a as) = entRaw a ∷ argsRaw as

  formRaw : Form → RawCert
  formRaw (pred P as) = rawCert (predName P) (argsRaw as)

  ---------------------------------------------------------------------------
  -- The checker

  entStep : (B : Ty) → List ℕ → Maybe ConstId → Maybe (Ent B)
  entStep B rs nothing  = nothing
  entStep B rs (just c) = mapMaybe (ent c) (checkRoute (cty c) B rs)

  checkEnt : (B : Ty) → RawArg → Maybe (Ent B)
  checkEnt B (rawArg n rs) = entStep B rs (constOf n)

  consStep : ∀ {A As} → Maybe (Ent A) → Maybe (Args As) → Maybe (Args (A ∷ As))
  consStep (just a) (just as) = just (acons a as)
  consStep (just a) nothing   = nothing
  consStep nothing  _         = nothing

  checkArgs : (As : List Ty) → List RawArg → Maybe (Args As)
  checkArgs []       []       = just anil
  checkArgs []       (_ ∷ _)  = nothing
  checkArgs (_ ∷ _)  []       = nothing
  checkArgs (A ∷ As) (a ∷ as) = consStep (checkEnt A a) (checkArgs As as)

  certStep : List RawArg → Maybe PredId → Maybe Form
  certStep as nothing  = nothing
  certStep as (just P) = mapMaybe (pred P) (checkArgs (psig P) as)

  checkCert : RawCert → Maybe Form
  checkCert (rawCert n as) = certStep as (predOf n)

  ---------------------------------------------------------------------------
  -- Soundness: accepted certificates are exactly the raw images of typed sentences.

  entStep-sound : ∀ {B} n rs (m : Maybe ConstId) {a : Ent B}
                → constOf n ≡ m → entStep B rs m ≡ just a → entRaw a ≡ rawArg n rs
  entStep-sound n rs nothing  _   ()
  entStep-sound {B} n rs (just c) eqC eq with mapMaybe-just (ent c) (checkRoute (cty c) B rs) eq
  ... | r , eqR , refl = cong₂ rawArg (constOf-sound n c eqC) (checkRoute-sound (cty c) B rs eqR)

  checkEnt-sound : ∀ {B} (x : RawArg) {a : Ent B} → checkEnt B x ≡ just a → entRaw a ≡ x
  checkEnt-sound (rawArg n rs) eq = entStep-sound n rs (constOf n) refl eq

  consStep-sound : ∀ {A As} (x : RawArg) (xs : List RawArg) (ma : Maybe (Ent A)) (mas : Maybe (Args As))
                   {r : Args (A ∷ As)}
                 → consStep ma mas ≡ just r
                 → (∀ {a} → ma ≡ just a → entRaw a ≡ x)
                 → (∀ {as} → mas ≡ just as → argsRaw as ≡ xs)
                 → argsRaw r ≡ x ∷ xs
  consStep-sound x xs (just a) (just as) eq ha has with just-inj eq
  ... | refl = cong₂ _∷_ (ha refl) (has refl)
  consStep-sound x xs (just a) nothing   () ha has
  consStep-sound x xs nothing  _         () ha has

  checkArgs-sound : ∀ As (xs : List RawArg) {r : Args As} → checkArgs As xs ≡ just r → argsRaw r ≡ xs
  checkArgs-sound []       []       eq with just-inj eq
  ... | refl = refl
  checkArgs-sound []       (_ ∷ _)  ()
  checkArgs-sound (_ ∷ _)  []       ()
  checkArgs-sound (A ∷ As) (x ∷ xs) eq =
    consStep-sound x xs (checkEnt A x) (checkArgs As xs) eq
      (λ eqa → checkEnt-sound x eqa) (λ eqs → checkArgs-sound As xs eqs)

  certStep-sound : ∀ n xs (m : Maybe PredId) {f : Form}
                 → predOf n ≡ m → certStep xs m ≡ just f → formRaw f ≡ rawCert n xs
  certStep-sound n xs nothing  _   ()
  certStep-sound n xs (just P) eqP eq with mapMaybe-just (pred P) (checkArgs (psig P) xs) eq
  ... | as , eqA , refl = cong₂ rawCert (predOf-sound n P eqP) (checkArgs-sound (psig P) xs eqA)

  -- T16 (soundness of the checker).
  checkCert-sound : ∀ (c : RawCert) {f : Form} → checkCert c ≡ just f → formRaw f ≡ c
  checkCert-sound (rawCert n xs) eq = certStep-sound n xs (predOf n) refl eq

  ---------------------------------------------------------------------------
  -- Completeness: every typed sentence is accepted, and recovered, from its raw image.

  consStep-complete : ∀ {A As} {ma : Maybe (Ent A)} {mas : Maybe (Args As)} {a as}
                    → ma ≡ just a → mas ≡ just as → consStep ma mas ≡ just (acons a as)
  consStep-complete refl refl = refl

  checkEnt-complete : ∀ {B} (a : Ent B) → checkEnt B (entRaw a) ≡ just a
  checkEnt-complete {B} (ent c r) =
    trans (cong (entStep B (routeNames r)) (constOf-name c))
          (cong (mapMaybe (ent c)) (checkRoute-complete r))

  checkArgs-complete : ∀ {As} (as : Args As) → checkArgs As (argsRaw as) ≡ just as
  checkArgs-complete anil         = refl
  checkArgs-complete (acons a as) = consStep-complete (checkEnt-complete a) (checkArgs-complete as)

  -- T16 (completeness of the checker).
  checkCert-complete : ∀ (f : Form) → checkCert (formRaw f) ≡ just f
  checkCert-complete (pred P as) =
    trans (cong (certStep (argsRaw as)) (predOf-name P))
          (cong (mapMaybe (pred P)) (checkArgs-complete as))

  ---------------------------------------------------------------------------
  -- T1: typing of certificates is decidable.

  Typed : RawCert → Set
  Typed c = Σ Form (λ f → formRaw f ≡ c)

  private
    nothingNotJust : ∀ {A : Set} {x : A} → nothing ≡ just x → ⊥
    nothingNotJust ()

  decTyped : (c : RawCert) → Dec (Typed c)
  decTyped c with checkCert c in eq
  ... | just f  = yes (f , checkCert-sound c eq)
  ... | nothing = no λ { (f , refl) → nothingNotJust (trans (sym eq) (checkCert-complete f)) }

  ---------------------------------------------------------------------------
  -- Surface preservation: coercion insertion does not change the underlying sentence.

  names-of : List RawArg → List ℕ
  names-of []                = []
  names-of (rawArg c _ ∷ xs) = c ∷ names-of xs

  entSurface : ∀ {B} → Ent B → ℕ
  entSurface (ent c _) = constName c

  argsSurface : ∀ {As} → Args As → List ℕ
  argsSurface anil         = []
  argsSurface (acons a as) = entSurface a ∷ argsSurface as

  formSurface : Form → ℕ × List ℕ
  formSurface (pred P as) = predName P , argsSurface as

  rawSurface : RawCert → ℕ × List ℕ
  rawSurface (rawCert n xs) = n , names-of xs

  argsSurface-raw : ∀ {As} (as : Args As) → argsSurface as ≡ names-of (argsRaw as)
  argsSurface-raw anil                 = refl
  argsSurface-raw (acons (ent c r) as) = cong (λ t → constName c ∷ t) (argsSurface-raw as)

  formSurface-raw : ∀ (f : Form) → formSurface f ≡ rawSurface (formRaw f)
  formSurface-raw (pred P as) = cong (λ t → predName P , t) (argsSurface-raw as)

  surface-preserved : ∀ (c : RawCert) {f : Form} → checkCert c ≡ just f → formSurface f ≡ rawSurface c
  surface-preserved c {f} eq = trans (formSurface-raw f) (cong rawSurface (checkCert-sound c eq))

  ---------------------------------------------------------------------------
  -- T2: coercions are conservative. A coercion is required exactly when the literal type of a
  -- constant clashes with the slot type; without a clash the empty route is the only (literal) reading.

  routeNil-no : ∀ A B (d : Dec (A ≡ B)) → ¬ (A ≡ B) → routeNil A B d ≡ nothing
  routeNil-no A B (yes p) n = ⊥-elim (n p)
  routeNil-no A B (no _)  n = refl

  -- Clash: the empty route is rejected.
  clash-route-rejected : ∀ A B → ¬ (A ≡ B) → checkRoute A B [] ≡ nothing
  clash-route-rejected A B n = routeNil-no A B (tyEq A B) n

  clash-ent-rejected : ∀ c B → ¬ (cty c ≡ B) → checkEnt B (rawArg (constName c) []) ≡ nothing
  clash-ent-rejected c B n =
    trans (cong (entStep B []) (constOf-name c)) (cong (mapMaybe (ent c)) (clash-route-rejected (cty c) B n))

  -- No clash: the literal reading is accepted.
  literal-accepted : ∀ c → checkEnt (cty c) (rawArg (constName c) []) ≡ just (ent c nil)
  literal-accepted c = checkEnt-complete (ent c nil)

  -- A route with no edges joins equal types.
  routeNames-empty : ∀ {A B} (r : Route A B) → routeNames r ≡ [] → A ≡ B
  routeNames-empty nil        _ = refl
  routeNames-empty (cons e r) ()

  -- A clashing slot cannot be filled by the literal (empty) route.
  clash-needs-route : ∀ {c B} → ¬ (cty c ≡ B) → (r : Route (cty c) B) → ¬ (routeNames r ≡ [])
  clash-needs-route n r h = n (routeNames-empty r h)
