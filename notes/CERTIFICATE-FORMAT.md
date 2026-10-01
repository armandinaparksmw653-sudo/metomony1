# Extended certificate: format and guarantees

Defined in `agda/src/Metonymy/{Evidence,FamilyCert,ThreeCert,Cert}.agda`; run end to end in
`agda/src/Metonymy/CertExample.agda`.

## What the producer (the Haskell core) emits

Everything is identifiers and indices; nothing typed crosses the boundary.

| Raw form | Content | What the checker proves |
|---|---|---|
| `resolve (rawResolve cert refs)` | `cert`: the coerced sentence (`rawCert predName [rawArg constName routeEdgeNames]`); `refs`: one referent index per argument (an index into the enumerated carrier of the argument's sort in the snapshot) | the typed sentence, and that each referent is reached from its constant along the argument's route in the snapshot and the predicate holds of the tuple (`ResolveHolds`) |
| `retain (rawResolve cert refs)` | the same data | the truncated existence of satisfying referents (`formSem`); the witness is only used to prove it |
| `family (rawFamily c p slot readings apart same)` | constant, predicate and slot being coerced; candidate routes as lists of edge names; `apart`: `(i, j, srcRef, tgtRef)` claiming readings `i` and `j` differ on a pair of referents; `same`: `(i, j, leftSteps, rightSteps)` claiming `i` and `j` are the same reading, with chains of rewriting steps `(ruleName, pre, post)` to a common list of names | a list of proved claims about the set of readings `Coe`: some pairs are distinct points, some are equal |
| `conjoin (rawConjoin c conj1 conj2)` | a constant and two coercions, each with a satisfaction witness | the conjunction of the two Retain claims for the referent of the constant (`Conjoin`) |
| `three (rawThree c (a1,a2,a3) conj1 conj2?)` | a constant whose sort is the sort of the quantified variable; three source referents; for each coercion: its route, a unary predicate, a satisfaction witness per source referent, and a distinguishing referent for each of the three pairs | `Three₁` (one coercion) or `Three₂` (copredication: two coercions) in the snapshot: three referents pairwise distinguishable under every coercion used |

The checker is `Cert.Cert.check : Raw → Maybe Checked`. A `Checked` value carries its proofs, and
`Cert.Cert.meaning : (ck : Checked) → Meaning ck` states what each kind establishes. For a corpus,
`acceptAll batch ≡ true` by `refl` is the proof that every certificate in the batch is accepted.

## What soundness means here

Soundness is by construction: the checker's result type contains the proofs, so an accepted certificate
establishes its claim whatever produced it. Specifically:

* every route is rebuilt from edge names and typechecked (`checkRoute`), so a route cannot be ill typed;
* every referent index is resolved in the snapshot, so a referent cannot be absent;
* every relational fact is evaluated by the Boolean evaluator, proved equal to the relational semantics
  (`Audit.evalR⇒`);
* "distinct" claims rest on apartness witnesses and need `SoundRules` for the snapshot, which the audit
  supplies (`Audit.audit-all`);
* "same" claims rest on chains of declared rewriting steps, lifted to the typed equivalence
  (`NormalizeFull.LiftSteps.lift-chain`), under the assumption that every left-hand side has an edge.

## What it does not establish

* All claims are about the knowledge-base **snapshot** (a finite model), not about the world.
* Which mode the system *should* output (Resolve vs Retain vs Family) is a pragmatic decision, not certified.
* A family certificate lists some readings and proves some relations between them; it does not by itself
  claim the list is exhaustive. Exhaustiveness up to a length bound is the separate certificate form of
  `Classify.readings-covered`, not yet part of the raw format.
* Individuation covers the quantifier "three" over three named referents with one or two coercions; general
  numeral quantifiers and universal quantification are not covered.
* Completeness of the checkers (that every correct certificate is accepted) is demonstrated on examples, not
  proved. This affects usability, not soundness.
* The translation of the raw format into Agda terms is a trust boundary only in the harmless direction: a
  mistranslation can cause rejection or a different certificate, and an accepted certificate is true in the
  snapshot regardless.
