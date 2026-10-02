# Pipeline on ConMeC (steps 1-4)

1. `lexicon/conmec_v1.json` is the single source of truth (12 sorts, 6 coercion edges, unary predicates, constants, no rules yet).
   `pipeline/lexicon.py` loads and validates it; `pipeline/gen_agda.py` generates `agda/src/Metonymy/ConMeCKB.agda`
   (the `Lexicon` with its name/identifier proofs) and `ConMeCSnap.agda` (a uniform one-element snapshot).
2. `pipeline/scorer.py`: `score(item, candidates) -> log-probabilities`. Implementations read the scores computed in
   Colab (Qwen2.5-7B forced choice, BERT out-of-fold), so the pipeline runs locally.
3. `pipeline/pipeline.py`: window, candidates, scorer, mode (Resolve, or Retain inside a band around the dev-fitted
   threshold), raw certificate.
4. `pipeline/check_agda.py`: writes a batch module with one claim per certificate plus corrupted controls and runs Agda.

```
python pipeline/gen_agda.py
python pipeline/pipeline.py --scorer qwen --n 204
python pipeline/check_agda.py results/pipeline_items.jsonl --agda <path to agda>
```

What acceptance means: ConMeC has no external knowledge base, so the snapshot is uniform and Agda certifies the type and
route structure of each certificate against the lexicon (the coercion exists, matches the sort, identifiers resolve),
not that the sentence is true. Content verification needs a dataset with a real KB (toponyms via Wikidata).
