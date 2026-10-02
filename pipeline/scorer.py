"""Scorer interface: how well does each candidate reading fit the sentence?

    scorer.score(item, candidates) -> list of log-probabilities, one per candidate (they sum to 1 in prob space)

`item` is a dict with at least `sentence` and `target` (and `id`, `category` for the dataset-backed scorers);
`candidates` is the list produced by Lexicon.candidates (the first one is always the literal reading).

Implementations here read scores that were computed once in Colab and saved by the experiments, so the pipeline
runs locally without a GPU and reproduces the numbers of the live models exactly:
  * QwenCached : Qwen2.5-7B-Instruct, forced choice between the literal and the metonymic reading (S1a/S1b,
                 both option orders averaged), from results/out_qwen25_7b.jsonl;
  * BertCached : BERT-base fine-tuned with cross-validation, out-of-fold probabilities in one of the three
                 evaluation regimes (doc / target / type), from results/colab_run1/oof_probs.csv.
Both support exactly two candidates (literal, one coercion), which is what the ConMeC lexicon gives.
"""
import csv
import json
import math
import os

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "..", "results")


def _logsig(x):
    return -math.log1p(math.exp(-x)) if x > -30 else x


class Scorer:
    name = "scorer"

    def score(self, item, candidates):
        raise NotImplementedError

    def margin(self, item, candidates):
        """Log-odds of the first coercion reading against the literal one (two candidates)."""
        lp = self.score(item, candidates)
        return lp[1] - lp[0]


class _TwoWay(Scorer):
    def _logodds(self, item):
        raise NotImplementedError

    def score(self, item, candidates):
        assert len(candidates) == 2, "cached scorers handle one literal and one coercion reading"
        s = self._logodds(item)
        return [_logsig(-s), _logsig(s)]


class QwenCached(_TwoWay):
    name = "qwen2.5-7b-s1"

    def __init__(self, path=os.path.join(RESULTS, "out_qwen25_7b.jsonl")):
        raw = {}
        with open(path, encoding="utf-8") as f:
            for line in f:
                r = json.loads(line)
                if r["prompt"] in ("S1a", "S1b"):
                    # S1a lists the metonymic reading as A, S1b as B
                    meto, lit = ("A", "B") if r["prompt"] == "S1a" else ("B", "A")
                    raw[(r["id"], r["prompt"])] = r["lp"][meto] - r["lp"][lit]
        self.s = {i: 0.5 * (raw[(i, "S1a")] + raw[(i, "S1b")]) for (i, p) in raw if p == "S1a" and (i, "S1b") in raw}

    def _logodds(self, item):
        return self.s[item["id"]]


class BertCached(_TwoWay):
    def __init__(self, regime="doc", path=os.path.join(RESULTS, "colab_run1", "oof_probs.csv"), column="encoder"):
        self.name = "bert-base-%s" % regime
        self.s = {}
        with open(path, newline="") as f:
            for r in csv.DictReader(f):
                if r["regime"] == regime:
                    p = min(max(float(r[column]), 1e-6), 1 - 1e-6)
                    self.s[int(r["id"])] = math.log(p / (1 - p))

    def _logodds(self, item):
        return self.s[item["id"]]
