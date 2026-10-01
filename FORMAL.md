# Formal core: theorem index

Agda 2.8.0.2, cubical v0.9, `--safe`, no `postulate`, no holes, no termination pragmas (enforced by CI).
Two modules additionally pass `-WnoUnsupportedIndexedMatch` (as the cubical library itself does): the warning
only concerns computation of some functions on transports, which nothing here relies on.
Build: `cd agda && agda src/Everything.agda`.

Two layers. The syntactic layer (`Base`, `Graph`, `Check`, `Example`) uses only Agda builtins and
`--cubical-compatible`, so it stays compilable. The semantic layer is Cubical Agda.

## Status of the planned theorems

"Proved" means a complete Agda proof in this repository. Where a result holds only under a stated
hypothesis, or is weaker than the plan hoped, this is said explicitly.

| № | Statement | Agda | Status |
|---|---|---|---|
| E1 | Extended certificate: modes, chosen referents, readings, individuation | `Cert.Cert.check`, `meaning`, `acceptAll`; parts: `Evidence.checkResolve`, `retained`; `FamilyCert.Check.checkFamily`; `ThreeCert.Check.checkThree`; `Cert.checkConjoin`; end-to-end: `CertExample` | Proved sound by construction (the checked value carries the proofs). Claims are about a finite knowledge-base snapshot. Completeness of the checkers is demonstrated on examples, not proved; format and limits in `notes/CERTIFICATE-FORMAT.md` |
| C1 | Coherence of coercions is `isProp (Coe A B)`; uniqueness is contractibility; `[r] = [s]` iff `∥ r ≈ s ∥` | `Coherence.coherent⇒isProp`, `isProp⇒coherent`, `readings-equal`, `contractible⇒exists×coherent`, `exists×coherent⇒contractible` | Proved. This is the central correspondence of the project; it was not stated as a theorem before the audit |
| T1 | Typing of certificates is decidable | `Check.decTyped` | Proved |
| T2 | Coercions are conservative: needed exactly on a type clash | `Check.clash-route-rejected`, `clash-ent-rejected`, `literal-accepted`, `clash-needs-route` | Proved |
| T3 | Elaboration soundness | `Check.checkCert-sound`, `surface-preserved` | Proved for certificates. The elaborator is the Haskell core; Agda checks its output |
| T4 | Bridge to implicit coercive subtyping (Luo) | `Implicit.elab-sound`, `elab-complete`, `elab-unique` | Proved for the **first-order fragment** (predicate sentences with constant arguments). The full theorem is **not done**; see `notes/T4-scout.md` |
| T5 | Coe is a set; readings form a category; interpretation is a functor | `Semantics.isSetCoe`, `Category._∘C_`, `assocC`, `idLC`, `idRC`, `interpC-∘`, `Graph.≈-++-cong` | Proved |
| T6 | Route independence | `Semantics.routeIndependence`, `sound≈`, `interpC`; for sentences `Sentence.formSem-indep` | Proved |
| T7 | Classification and decidability of equivalence | strings: `StringRewriting.levi`, `Confluence.LCs` (critical pair lemma), `Search.step?`, `terminatesS`, `Search.Norm.normS-resp`; abstract: `Rewriting.newman`, `church-rosser`, `nf-unique`, `Normalize.norm-resp`; typed lifting: `TypedFactor.factor-lhs`, `NormalizeFull.lift-step`, `lift-chain`; result: `NormalizeFull.Build.normalizer`; classification: `Equivalence.decEquiv`, `classification` | Proved, with **no unproved hypotheses beyond finite checks on the lexicon**: the rule list is finite and complete, every rule shortens the route (`Shrinks`), and the critical pairs (overlaps and inclusions of left-hand sides, `CP1`, `CP2`) are joinable. The critical pair lemma and the redex search are proved. The critical-pair check is also **computable inside Agda**: `StringRewriting.Checker.cpDecide` enumerates all splittings and joins each pair by greedy reduction; a successful run yields `CP1 × CP2`. Concrete runs: `NormalizeExample` (accepted, normal forms computed by `refl`) and `NormalizeExampleBad` (a non-confluent system is rejected). Without such conditions decidability is false in general: equivalence of routes is the word problem of a finitely presented category. `Normalize.agda` is the earlier, more abstract version that assumed local confluence and the redex search |
| T7' | Completeness of the list of readings up to a length bound | `Enumerate.routesUpTo-complete`, `Classify.readings-covered`, `reps-distinct`, `Enumerate.routeEq` | Proved, in certificate form: a covering list of representatives, pairwise apart in a model, gives exactly those readings up to the bound |
| T8 | Context as enabling of coercions (corrected formulation) | `Context.restrict-enabled`, `restrict-disabled`, `restrict-sound`, `Enabled-resp`, `EnabledC` | Proved |
| T9' | Lattice of modes | `Semantics.Resolve⇒Retain`, `Modes.every⇒reading`, `reading⇒some`, `resolve⇒reading`, `reading-rep`, `retain-indep` | Proved |
| T10 | Retain is irreversible | `Modes.retraction⇒isProp`, `noChoice` | Proved (a retraction of the truncation forces a proposition) |
| T11 | Conjoin and homonyms | `Modes.Conjoin`, `conjoin⇒first`, `conjoin⇒second`, `conjoin-impossible`, `homonym-disjoint` | Proved. The common-source condition is enforced by the typing of `Conjoin` |
| T12 | Individuation under coercions, no injectivity axiom | counting through functions: `Counting.copredication`; through relational coercions: `Quantified.Three₂→₁`, `Three₂→₂`; invariance: `QuantifiedRoutes.threeVia-indep`, `threeVia₂-indep`; functional agreement: `Quantified.Functional.three⇒`, `⇒three` | Proved. The list of coercions entering the criterion is read off the routes of the elaborated sentence |
| T13 | Countermodel to `Three Book ⇒ Three Info` | `Counting.CL15-schema-fails` | Proved |
| T14 | Quotient characterization of counting | `Image.quotientImage`, `count⇒image`, `image⇒count` | Proved |
| T15 | Re-encoding of the ontology | direct: `Reencode.interp-equivariant`, `sound-transfer`; by univalence: `ReencodeUA.model≡`, `invariance`, `soundness-invariant` | Proved both ways. The univalence version builds a path between models with `ua`, so every property of models transfers by transport |
| T16 | Checker soundness and completeness | `Check.checkCert-sound`, `checkCert-complete` | Proved |
| T17 | Lexicon audit by computation | `Audit.audit-sound`, `audit-all`; examples `AuditExample.good-passes`, `bad-fails`, `good-sound` | Proved |
| T18 | Apartness witnesses for distinct readings | `Equivalence.apart⇒¬≈`, `apart⇒distinct` | Proved |

## What the formal core does not cover

* Truth of lexicon edges and of knowledge-base facts, and correctness of the scorer: these are empirical.
* The extended certificate (E1) covers Resolve, Retain, a family of readings, Conjoin and Three. Not covered:
  exhaustiveness of a family (the bounded-classification certificate is not in the raw format), general numeral
  quantifiers, and certification of which mode should be chosen.
* The full T4, discourse dynamics, linear dot-types.

## Modules

| Module | Content |
|---|---|
| `Metonymy.Base` | Builtin-only prelude (syntactic layer) |
| `Metonymy.Graph` | Sense graph, routes, declared equivalences, congruence closure, composition congruence |
| `Metonymy.Check` | Lexicon interface, typed sentences, raw certificates, checker, T1, T2, T16, surface preservation |
| `Metonymy.Example` | Toy lexicon and certificates checked by computation |
| `Metonymy.Semantics` | Models, relational interpretation, Coe, T6, Resolve/Retain |
| `Metonymy.Sentence` | Meaning of typed sentences, route independence for sentences |
| `Metonymy.Category` | Composition on Coe, category laws, functoriality of the interpretation (T5) |
| `Metonymy.Modes` | Modes over readings, Conjoin (T9', T10, T11) |
| `Metonymy.Equivalence` | Apartness (T18), normalizer-based classification (T7) |
| `Metonymy.Rewriting` | Abstract rewriting: Newman, Church-Rosser, normal forms (T7) |
| `Metonymy.Normalize` | Earlier version: typed rewriting assuming local confluence and redex search (superseded by `NormalizeFull`) |
| `Metonymy.StringRewriting` | Rewriting on lists of names: Levi's lemma, critical pair lemma, redex search, termination, computable critical-pair check (T7) |
| `Metonymy.TypedFactor` | Factoring typed routes along a left-hand side (T7) |
| `Metonymy.NormalizeFull` | The complete normalizer for typed routes (T7) |
| `Metonymy.ExampleRules`, `NormalizeExample` | Concrete lexicon: critical pairs checked by computation, normal forms computed |
| `Metonymy.ExampleRulesBad`, `NormalizeExampleBad` | Negative test: non-confluent system rejected |
| `Metonymy.Enumerate` | Decidable route equality, enumeration of routes up to a bound (T7') |
| `Metonymy.Classify` | Classification certificate for readings up to a bound (T7') |
| `Metonymy.Context` | Context as enabling of edges (T8) |
| `Metonymy.Reencode`, `ReencodeUA` | Re-encoding invariance, directly and by univalence (T15) |
| `Metonymy.Counting` | Individuation through functions (T12, T13) |
| `Metonymy.Quantified`, `QuantifiedRoutes` | Individuation through relational coercions and routes (T12) |
| `Metonymy.Evidence`, `FamilyCert`, `ThreeCert`, `Cert` | Extended certificate (E1) |
| `Metonymy.ExampleKB`, `CertExample` | Example lexicon, snapshot, and end-to-end certificate run |
| `Metonymy.Coherence` | Coherence iff isProp of the readings, uniqueness iff contractibility (C1) |
| `Metonymy.Instantiate` | Non-vacuity: parameterized modules instantiated, typed decision procedure computed |
| `Metonymy.Image` | Counting in the image as a quotient (T14) |
| `Metonymy.Implicit` | First-order fragment of the bridge to implicit coercions (T4) |
| `Metonymy.Audit`, `AuditExample` | Lexicon audit on finite models (T17) |
