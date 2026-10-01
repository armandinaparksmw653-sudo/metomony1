# Qwen2.5-7B-Instruct on ConMeC, zero-shot scores (run of 2026-10-01)

Files: `out_qwen25_7b.jsonl` (raw log-probs, 24000 rows, integrity checked: no duplicates, all 6000 sentences
x 4 prompts present, answer-token probability mass 0.9993+ except one P1 outlier), `metrics_qwen25_7b.txt`
(`experiments/llm/analyze.py`), `diagnostics_qwen25_7b.txt` (`experiments/llm/diagnostics.py`).
Test = 5000 sentences, split by document; dev = 1000. Prompts: `experiments/llm/prompts.py`.

## Zero-shot scores (single answer token, no reasoning, no examples)

| Prompt | AUROC | R0 macro-F1 (threshold 0) | R0t macro-F1 (dev threshold) |
|---|---|---|---|
| P0 plain yes/no | 0.681 | 0.629 | 0.623 |
| P1 type-conditioned yes/no | 0.638 | 0.580 | 0.569 |
| S1 forced choice (both orders averaged) | 0.698 | 0.594 | 0.640 |

Majority class (always literal): accuracy 0.713, macro-F1 0.416.
By type (S1 AUROC): LOCATION 0.85, PRODUCT 0.82, CONTAINER 0.75, PRODUCER 0.68, POSSESSED 0.64,
CAUSER 0.56 (close to chance; CAUSER and POSSESSED are also where the ConMeC paper reports the most errors).

Observations: the type-conditioned prompt P1 is worse than the plain P0; S1 has a clear position bias
(mean score of S1a -0.99, of S1b +0.94) that averaging cancels; the scores separate the classes but are poorly
calibrated (predicted-metonymic rate at threshold 0: P0 0.21, P1 0.31, S1a 0.46, S1b 0.52, true 0.287).

## Context: lexical shortcuts in ConMeC

| Baseline | Setting | AUROC | macro-F1 |
|---|---|---|---|
| target-word prior from the 1000 dev sentences | in-distribution (4460 of 5000 test rows have a (type, target) pair seen in dev) | 0.780 | 0.688 |
| TF-IDF + (type, target) one-hot, supervised | grouped 5-fold by document | 0.863 | 0.759 |
| TF-IDF sentence only, supervised | grouped 5-fold by **target word** (unseen words) | 0.695 | 0.552 |
| dev-calibrated combiner of the 4 Qwen scores, per-type weights (supervised on dev) | test | 0.802 | 0.724 |

The dataset has only 439 distinct (type, target) pairs, and the identity of the target word alone is already
a strong predictor. Therefore:

* In-distribution numbers partly measure lexical bias. A claim about interpretation quality should be
  backed by splits where the shortcut is removed: **unseen target words** and **cross-type** (train on five
  types, test on the sixth).
* The zero-shot LLM does not use word identity, and on unseen words it is on par with the supervised
  lexical baseline (AUROC 0.70 versus 0.695), and better on CONTAINER, PRODUCT, LOCATION, POSSESSED, worse on
  PRODUCER and CAUSER.

## Limits of this run

* It is the weakest reasonable use of the model: no examples, no reasoning, one token. Few-shot demonstrations
  and chain-of-thought (as in the ConMeC paper) are expected to improve it; this is not yet measured.
* One model, one prompt wording per family. Prompt sensitivity is not assessed.
* The ConMeC paper reports a supervised BERT with macro-F1 around 0.83 (read off its Table 7; to be checked
  against the paper). Our zero-shot numbers are far below that; the comparison is across regimes (supervised
  in-distribution versus zero-shot).
