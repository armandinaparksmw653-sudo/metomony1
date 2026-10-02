"""Pipeline MVP on ConMeC: window -> candidates -> scorer -> mode -> raw certificate.

    python pipeline/pipeline.py --scorer qwen --n 200

For a ConMeC item (sentence, target noun, type) the pipeline does:
  1. window      : the clause around the target (stanza UD parse when its models are installed, otherwise a
                   token window); only recorded as provenance in this version, the scorer sees the sentence;
  2. candidates  : the literal reading plus one reading per coercion edge leaving the literal sort (lexicon);
  3. scorer      : log-probabilities of the candidates (pluggable, see scorer.py);
  4. mode        : Resolve to the best candidate when the log-odds margin is outside the band around the
                   dev-fitted threshold, Retain (truncated existence of a coerced referent) inside the band;
  5. certificate : a raw certificate of identifiers (see notes/CERTIFICATE-FORMAT.md) for Agda to check.

The decision threshold is fitted on the dev split only; metrics are reported on the test split.
"""
import argparse
import json
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "experiments", "llm"))
import data  # noqa: E402
import analyze  # noqa: E402
import lexicon  # noqa: E402
import scorer as scorers  # noqa: E402

BAND = 1.0          # half-width (log-odds) of the Retain band around the threshold


def window(item, k=6):
    """Clause window around the target: up to k tokens on each side, cut at clause punctuation."""
    toks = re.findall(r"\w+(?:'\w+)?|[^\w\s]", item["sentence"])
    low = [t.lower() for t in toks]
    tw = item["target"].lower().split()[0]
    pos = next((i for i, t in enumerate(low) if t == tw), None)
    if pos is None:
        pos = next((i for i, t in enumerate(low) if tw in t), 0)
    a, b = max(0, pos - k), min(len(toks), pos + k + 1)
    for i in range(pos - 1, a - 1, -1):
        if toks[i] in {",", ";", ":", "(", ")"}:
            a = i + 1
            break
    for i in range(pos + 1, b):
        if toks[i] in {",", ";", ":", "(", ")"}:
            b = i
            break
    return {"tokens": toks[a:b], "target_index": pos - a}


def build(item, lx, sc, threshold, band=BAND):
    cands = lx.candidates(item["category"])
    lp = sc.score(item, cands)
    margin = lp[1] - lp[0]
    centered = margin - threshold
    meto = centered > 0
    mode = "retain" if abs(centered) < band else "resolve"
    chosen = cands[1] if meto else cands[0]
    lit_sort = cands[0]["sort"]
    cert = {
        "mode": mode,
        "pred": lx.pred_id["ctx" + chosen["sort"]],
        "const": lx.const_id["target" + lit_sort],
        "route": [lx.edge_id[n] for n in chosen["route"]],
        "refs": [0],
    }
    return {"id": item["id"], "category": item["category"], "label": item["label"], "margin": margin,
            "pred_meto": int(meto), "mode": mode, "chosen": chosen["name"], "cert": cert,
            "window": window(item)}


def fit_threshold(rows, dev, lx, sc):
    ys, ms = [], []
    for r in rows:
        if r["id"] in dev:
            ys.append(r["label"])
            ms.append(sc.margin(r, lx.candidates(r["category"])))
    return analyze.best_threshold(ys, ms)


def make_scorer(name, regime="doc"):
    if name == "qwen":
        return scorers.QwenCached()
    if name == "bert":
        return scorers.BertCached(regime)
    raise ValueError(name)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scorer", default="qwen", choices=["qwen", "bert"])
    ap.add_argument("--regime", default="doc")
    ap.add_argument("--n", type=int, default=200, help="test items for the certificate sample (stratified by type)")
    ap.add_argument("--out", default=os.path.join(HERE, "..", "results", "pipeline_items.jsonl"))
    a = ap.parse_args()

    rows = data.load()
    dev, test = data.split(rows)
    lx = lexicon.load()
    sc = make_scorer(a.scorer, a.regime)
    thr = fit_threshold(rows, dev, lx, sc)
    test_rows = [r for r in rows if r["id"] in test]
    built = [build(r, lx, sc, thr) for r in test_rows]
    y = [b["label"] for b in built]
    pred = [b["pred_meto"] for b in built]
    s = [b["margin"] for b in built]
    m = analyze.prf(y, pred)
    print("scorer %s, threshold %.3f (fitted on dev)" % (sc.name, thr))
    print("test n=%d  macro-F1 %.3f  acc %.3f  AUROC %.3f" % (len(y), m["macro_f1"], m["acc"], analyze.auroc(y, s)))
    modes = {}
    for b in built:
        modes[b["mode"]] = modes.get(b["mode"], 0) + 1
    print("modes on test:", modes)

    rng = random.Random(7)
    per = a.n // len(data.CATEGORIES)
    sample = []
    for c in data.CATEGORIES:
        pool = [b for b in built if b["category"] == c]
        sample += rng.sample(pool, per)
    os.makedirs(os.path.dirname(a.out), exist_ok=True)
    with open(a.out, "w", encoding="utf-8") as f:
        for b in sample:
            f.write(json.dumps(b) + "\n")
    print("wrote %d sampled items to %s" % (len(sample), os.path.relpath(a.out)))


if __name__ == "__main__":
    main()
