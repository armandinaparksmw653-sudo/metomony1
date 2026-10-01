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
| T1 | Typing of certificates is decidable | `Check.decTyped` | Proved |
| T2 | Coercions are conservative: needed exactly on a type clash | `Check.clash-route-rejected`, `clash-ent-rejected`, `literal-accepted`, `clash-needs-route` | Proved |
| T3 | Elaboration soundness | `Check.checkCert-sound`, `surface-preserved` | Proved for certificates. The elaborator is the Haskell core; Agda checks its output |
| T4 | Bridge to implicit coercive subtyping (Luo) | `Implicit.elab-sound`, `elab-complete`, `elab-unique` | Proved for the **first-order fragment** (predicate sentences with constant arguments). The full theorem is **not done**; see `notes/T4-scout.md` |
| T5 | Coe is a set; readings form a category; interpretation is a functor | `Semantics.isSetCoe`, `Category._∘C_`, `assocC`, `idLC`, `idRC`, `interpC-∘`, `Graph.≈-++-cong` | Proved |
| T6 | Route independence | `Semantics.routeIndependence`, `sound≈`, `interpC`; for sentences `Sentence.formSem-indep` | Proved |
| T7 | Classification and decidability of equivalence | abstract: `Rewriting.newman`, `church-rosser`, `nf-unique`, `Normalize.norm-resp`; for routes: `Normalize.Build.normalizer`; classification: `Equivalence.decEquiv`, `classification` | Proved **from three hypotheses on the lexicon**: every rule shortens the route (`Shrinks`), one-step rewriting is locally confluent (`LC`, the critical-pair condition), reducibility is decidable (`step?`, a finite search). Termination is derived from `Shrinks`. The critical-pair lemma (that joinable critical pairs imply `LC`) and the finite search are **not** formalized; they are hypotheses. Decidability cannot hold without such conditions: equivalence of routes is the word problem of a finitely presented category |
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
* The raw certificate format covers predicate sentences with coerced arguments. Modes, equivalence derivations,
  apartness witnesses, classes of readings and quantifiers are not yet part of the raw certificate; the
  semantic theorems above exist, the certificate encoding of them does not.
* The critical-pair lemma and the redex search behind T7, the full T4, discourse dynamics, linear dot-types.

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
| `Metonymy.Normalize` | Routes as a rewriting system, termination from length, the normalizer (T7) |
| `Metonymy.Enumerate` | Decidable route equality, enumeration of routes up to a bound (T7') |
| `Metonymy.Classify` | Classification certificate for readings up to a bound (T7') |
| `Metonymy.Context` | Context as enabling of edges (T8) |
| `Metonymy.Reencode`, `ReencodeUA` | Re-encoding invariance, directly and by univalence (T15) |
| `Metonymy.Counting` | Individuation through functions (T12, T13) |
| `Metonymy.Quantified`, `QuantifiedRoutes` | Individuation through relational coercions and routes (T12) |
| `Metonymy.Image` | Counting in the image as a quotient (T14) |
| `Metonymy.Implicit` | First-order fragment of the bridge to implicit coercions (T4) |
| `Metonymy.Audit`, `AuditExample` | Lexicon audit on finite models (T17) |
