# Metonymy as coercion routes

Verified interpretation of metonymy: a parsing/interpretation pipeline (UD window -> GF-like term ->
coercion routes) whose outputs are **certificates checked in Cubical Agda**.

* Plan and decisions: [`PLAN.md`](PLAN.md) (in Russian)
* Literature notes: [`notes/LITERATURE.md`](notes/LITERATURE.md)
* Toy finite-model experiments: [`experiments/toy/`](experiments/toy/)
* Formal core (Agda): [`agda/`](agda/)

## Formal core: build

Agda 2.8.0.2 and `cubical` v0.9 (pinned). Register the cubical library in your Agda `libraries` file, then:

```
cd agda
agda src/Everything.agda
```

Hygiene rules enforced by CI: `--safe`, no `postulate`, no holes, no `TERMINATING` pragmas.

## Status

Formal track (see `PLAN.md`):

| Item | Status |
|---|---|
| F1 signatures (`Graph`, `Route`, `Rules`, `Model`, `Coe`, modes) | done: `agda/src/Metonymy/Graph.agda`, `Semantics.agda` |
| T5 (partial), route category laws: `++-assoc`, `++-unitʳ` | proved |
| T6 route independence (`routeIndependence`, `interpC`) | proved |
| T9' (part): `Resolve ⇒ Retain` | proved |
| T12 counting under coercions (`copredication`) | proved |
| T13 countermodel to `Three Book ⇒ Three Info` | proved |
| Terms, typing, elaboration (T1, T3), certificates (T16) | next |

No empirical results yet.
