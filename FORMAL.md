# Formal core: theorem index

Agda 2.8.0.2, cubical v0.9, `--safe`, no `postulate`, no holes, no termination pragmas (enforced by CI).
Build: `cd agda && agda src/Everything.agda`.

Two layers. The syntactic layer (`Base`, `Graph`, `Check`, `Example`) uses only Agda builtins and
`--cubical-compatible`, so it stays compilable. The semantic layer is Cubical Agda.

## Status of the planned theorems

"Proved" means a complete Agda proof in this repository. Where a result holds only under a stated
hypothesis, or is weaker than the plan hoped, this is said explicitly.

| № | Statement | Agda | Status |
|---|---|---|---|
| T1 | Typing of certificates is decidable | `Check.decTyped` | Proved |
| T2 | Coercions are conservative: needed exactly on a type clash | `Check.clash-route-rejected`, `clash-ent-rejected`, `literal-accepted`, `clash-needs-route` | Proved (as these lemmas) |
| T3 | Elaboration soundness | `Check.checkCert-sound`, `surface-preserved` | Proved for certificates. The elaborator itself is the Haskell core; Agda checks its output |
| T4 | Completeness w.r.t. implicit coercions (Luo) | none | **Not done** (stretch) |
| T5 | Coe is a set; readings form a category; interpretation is a functor | `Semantics.isSetCoe`, `Category._∘C_`, `assocC`, `idLC`, `idRC`, `interpC-∘`, `Graph.≈-++-cong` | Proved |
| T6 | Route independence | `Semantics.routeIndependence`, `sound≈`, `interpC`; for sentences `Sentence.formSem-indep` | Proved |
| T7 | Classification and decidability of equivalence | `Equivalence.decEquiv`, `classification` | Proved **conditionally**: assumes a `Normalizer` (decidable route equality and a normal-form function respecting ≈). Constructing a normalizer for a concrete rule set is not formalized |
| T7' | Completeness of the list of readings up to a length bound | none | **Not done** |
| T8 | Context as enabling of coercions (corrected formulation) | `Context.restrict-enabled`, `restrict-disabled`, `restrict-sound`, `Enabled-resp`, `EnabledC` | Proved |
| T9' | Lattice of modes | `Semantics.Resolve⇒Retain`, `Modes.every⇒reading`, `reading⇒some`, `resolve⇒reading`, `reading-rep`, `retain-indep` | Proved |
| T10 | Retain is irreversible | `Modes.retraction⇒isProp`, `noChoice` | Proved (a retraction of the truncation forces a proposition) |
| T11 | A homonym is never both senses | `Modes.homonym-disjoint` | Proved. The "common source" condition for Conjoin is enforced by typing, not by a separate theorem |
| T12 | Counting under coercions without injectivity | `Counting.ThreeBoth→₁`, `ThreeBoth→₂`, `copredication` | Proved. Note: the content is that the correct truth conditions use distinctness under every coercion the predicates use; deriving that list from an elaborated sentence is not formalized |
| T13 | Countermodel to `Three Book ⇒ Three Info` | `Counting.CL15-schema-fails` | Proved |
| T14 | Quotient characterization of counting | none | **Not done** (not needed once T12 is stated through the coercions) |
| T15 | Re-encoding of the ontology | `Reencode.interp-equivariant`, `sound-transfer` | Proved **directly by induction**. The general structure-identity-principle formulation via univalence is not formalized |
| T16 | Checker soundness and completeness | `Check.checkCert-sound`, `checkCert-complete` | Proved |
| T17 | Lexicon audit by computation | `Audit.audit-sound`, `audit-all`; examples `AuditExample.good-passes`, `bad-fails`, `good-sound` | Proved |
| T18 | Apartness witnesses for distinct readings | `Equivalence.apart⇒¬≈`, `apart⇒distinct` | Proved |

## What the formal core does not cover

* Truth of lexicon edges and of knowledge-base facts, and correctness of the scorer: these are empirical.
* The certificate format covers predicate sentences with coerced arguments. Modes, equivalence derivations,
  classes of readings and quantifiers are not yet part of the raw certificate.
* Discourse dynamics, linear dot-types (newspaper), and the bridge to implicit coercive subtyping (T4).

## Modules

| Module | Content |
|---|---|
| `Metonymy.Base` | Builtin-only prelude (syntactic layer) |
| `Metonymy.Graph` | Sense graph, routes, declared equivalences, congruence closure, composition congruence |
| `Metonymy.Check` | Lexicon interface, typed sentences, raw certificates, checker, T1, T2, T16, surface preservation |
| `Metonymy.Example` | Toy lexicon and certificates checked by computation |
| `Metonymy.Semantics` | Models, relational interpretation, Coe, T6, Resolve/Retain |
| `Metonymy.Sentence` | Meaning of typed sentences, route independence for sentences |
| `Metonymy.Category` | Composition on Coe, category laws, functoriality of the interpretation |
| `Metonymy.Modes` | Modes over readings, T9', T10, T11 |
| `Metonymy.Equivalence` | Apartness (T18), normalizer-based classification (T7) |
| `Metonymy.Context` | Context as enabling of edges (T8) |
| `Metonymy.Reencode` | Re-encoding invariance (T15) |
| `Metonymy.Counting` | Individuation (T12, T13) |
| `Metonymy.Audit`, `AuditExample` | Lexicon audit on finite models (T17) |
