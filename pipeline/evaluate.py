"""Step 5: evaluation of the pipeline decision in the three ConMeC regimes.

    python pipeline/evaluate.py

Regimes (the threshold is always fitted on data the evaluated item's group does not belong to):
  doc    : threshold fitted on the dev split, scored on the test split (document-grouped);
  target : 5 folds grouped by target word; the threshold of a fold is fitted on the other folds;
  type   : leave-one-type-out; the threshold for a type is fitted on the other five types (unseen coercion type).
For BERT the scores are out-of-fold probabilities of the matching regime, so no item is scored by a model that
saw its document / target / type. Qwen is zero-shot and regime independent.
Also reported: the Retain share and the accuracy on Resolve versus Retain items, with 95% bootstrap intervals.
"""
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "..", "experiments", "llm"))
import data  # noqa: E402
import analyze  # noqa: E402
import lexicon  # noqa: E402
import scorer as scorers  # noqa: E402
from pipeline import BAND  # noqa: E402


def groups(rows, regime, dev):
    """Yield (train_ids, test_ids) pairs for the regime."""
    ids = [r["id"] for r in rows]
    if regime == "doc":
        yield dev, set(ids) - dev
    elif regime == "target":
        targets = sorted({r["target"].lower() for r in rows})
        random.Random(13).shuffle(targets)
        fold = {t: i % 5 for i, t in enumerate(targets)}
        for k in range(5):
            te = {r["id"] for r in rows if fold[r["target"].lower()] == k}
            yield set(ids) - te, te
    else:
        for c in data.CATEGORIES:
            te = {r["id"] for r in rows if r["category"] == c}
            yield set(ids) - te, te


def boot(y, pred, s, n=300):
    rng = random.Random(5)
    idx = range(len(y))
    f, a = [], []
    for _ in range(n):
        b = [rng.choice(idx) for _ in idx]
        yy, pp, ss = [y[i] for i in b], [pred[i] for i in b], [s[i] for i in b]
        f.append(analyze.prf(yy, pp)["macro_f1"])
        a.append(analyze.auroc(yy, ss))
    f.sort(), a.sort()
    return (f[int(.025 * n)], f[int(.975 * n)]), (a[int(.025 * n)], a[int(.975 * n)])


def evaluate(rows, lx, sc, regime, dev):
    marg = {r["id"]: sc.margin(r, lx.candidates(r["category"])) for r in rows}
    by = {r["id"]: r for r in rows}
    out = []
    for train, test in groups(rows, regime, dev):
        thr = analyze.best_threshold([by[i]["label"] for i in train], [marg[i] for i in train])
        for i in test:
            c = marg[i] - thr
            out.append((i, by[i]["label"], int(c > 0), marg[i], abs(c) < BAND, by[i]["category"]))
    return out


def report(name, regime, res):
    y = [r[1] for r in res]
    p = [r[2] for r in res]
    s = [r[3] for r in res]
    m = analyze.prf(y, p)
    (fl, fh), (al, ah) = boot(y, p, s)
    ret = [r for r in res if r[4]]
    rsv = [r for r in res if not r[4]]
    acc = lambda g: sum(1 for r in g if r[1] == r[2]) / max(1, len(g))
    print("%-14s %-7s n=%4d  macro-F1 %.3f [%.3f,%.3f]  AUROC %.3f [%.3f,%.3f]  retain %.1f%%  acc resolve %.3f / retain %.3f" % (
        name, regime, len(res), m["macro_f1"], fl, fh, analyze.auroc(y, s), al, ah, 100 * len(ret) / len(res), acc(rsv), acc(ret)))
    return res


def main():
    rows = data.load()
    dev, _ = data.split(rows)
    lx = lexicon.load()
    for regime in ("doc", "target", "type"):
        for name, sc in (("qwen2.5-7b", scorers.QwenCached()), ("bert-base", scorers.BertCached(regime))):
            res = report(name, regime, evaluate(rows, lx, sc, regime, dev))
            if regime == "type":
                per = {}
                for c in data.CATEGORIES:
                    g = [r for r in res if r[5] == c]
                    per[c] = analyze.auroc([r[1] for r in g], [r[3] for r in g])
                print("    per-type AUROC:", {k: round(v, 3) for k, v in per.items()})


if __name__ == "__main__":
    main()
