# Metonymy as coercion routes

Verified interpretation of metonymy: a parsing/interpretation pipeline (UD window -> GF-like term ->
coercion routes) whose outputs are **certificates checked in Cubical Agda**.

* Plan and decisions: [`PLAN.md`](PLAN.md) (in Russian)
* Literature notes: [`notes/LITERATURE.md`](notes/LITERATURE.md)
* Toy finite-model experiments: [`experiments/toy/`](experiments/toy/)
* Formal core (Agda): [`agda/`](agda/), theorem index in [`FORMAL.md`](FORMAL.md)

## Formal core: build

Agda 2.8.0.2 and `cubical` v0.9 (pinned). Register the cubical library in your Agda `libraries` file, then:

```
cd agda
agda src/Everything.agda
```

Hygiene rules enforced by CI: `--safe`, no `postulate`, no holes, no `TERMINATING` pragmas.

## Status

Formal track: the planned core is implemented and machine-checked; see [`FORMAL.md`](FORMAL.md) for the theorem
index with exact Agda names and an honest status for each result (including what is conditional or not done).
Engineering track (data, baselines, pipeline, Haskell core) has not started. No empirical results yet.
