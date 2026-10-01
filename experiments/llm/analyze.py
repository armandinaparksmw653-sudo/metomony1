"""Metrics for the ConMeC scores produced by score.py.

Per prompt family (and the average of the two option orders, S1):
  * R0: zero-shot decision, metonymic iff the score is positive (no tuning of any kind);
  * R0t: the threshold is chosen on dev (maximizing macro-F1) and applied to test;
  * AUROC, which does not depend on a threshold.
Reported on test, overall and per type, with bootstrap 95% intervals (resampling sentences).
"""
import argparse
import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data
import prompts


def load_scores(path):
    raw = {}
    with open(path, encoding="utf-8") as f:
        for line in f:
            r = json.loads(line)
            a, b = prompts.ANSWER_TOKENS[r["prompt"]]
            meto = prompts.metonymic_token(r["prompt"])
            other = b if meto == a else a
            raw[(r["id"], r["prompt"])] = r["lp"][meto] - r["lp"][other]
    scores = {}
    ids = {k[0] for k in raw}
    for i in ids:
        for pid in ("P0", "P1"):
            if (i, pid) in raw:
                scores[(i, pid)] = raw[(i, pid)]
        if (i, "S1a") in raw and (i, "S1b") in raw:
            scores[(i, "S1")] = 0.5 * (raw[(i, "S1a")] + raw[(i, "S1b")])
    return scores


def f1(tp, fp, fn):
    return 0.0 if tp == 0 else 2 * tp / (2 * tp + fp + fn)


def prf(y, pred):
    tp = sum(1 for a, b in zip(y, pred) if a == 1 and b == 1)
    fp = sum(1 for a, b in zip(y, pred) if a == 0 and b == 1)
    fn = sum(1 for a, b in zip(y, pred) if a == 1 and b == 0)
    tn = len(y) - tp - fp - fn
    f_pos, f_neg = f1(tp, fp, fn), f1(tn, fn, fp)
    return {"acc": (tp + tn) / len(y), "f1_meto": f_pos, "macro_f1": 0.5 * (f_pos + f_neg)}


def auroc(y, s):
    order = sorted(range(len(y)), key=lambda i: s[i])
    ranks = [0.0] * len(y)
    i = 0
    while i < len(order):
        j = i
        while j + 1 < len(order) and s[order[j + 1]] == s[order[i]]:
            j += 1
        for k in range(i, j + 1):
            ranks[order[k]] = (i + j) / 2 + 1
        i = j + 1
    pos = [r for r, a in zip(ranks, y) if a == 1]
    n1, n0 = len(pos), len(y) - len(pos)
    if n1 == 0 or n0 == 0:
        return float("nan")
    return (sum(pos) - n1 * (n1 + 1) / 2) / (n1 * n0)


def best_threshold(y, s):
    cands = sorted(set(s))
    best, bt = -1, 0.0
    for k in range(len(cands) + 1):
        t = (cands[k - 1] + cands[k]) / 2 if 0 < k < len(cands) else (cands[0] - 1 if k == 0 else cands[-1] + 1)
        m = prf(y, [1 if v > t else 0 for v in s])["macro_f1"]
        if m > best:
            best, bt = m, t
    return bt


def bootstrap(y, s, t, n=500, seed=1):
    rng = random.Random(seed)
    stats = {"acc": [], "macro_f1": [], "f1_meto": [], "auroc": []}
    idx = list(range(len(y)))
    for _ in range(n):
        b = [rng.choice(idx) for _ in idx]
        yy, ss = [y[i] for i in b], [s[i] for i in b]
        m = prf(yy, [1 if v > t else 0 for v in ss])
        for k in ("acc", "macro_f1", "f1_meto"):
            stats[k].append(m[k])
        stats["auroc"].append(auroc(yy, ss))
    out = {}
    for k, v in stats.items():
        v = sorted(x for x in v if x == x)
        out[k] = (v[int(0.025 * len(v))], v[int(0.975 * len(v)) - 1]) if v else (float("nan"),) * 2
    return out


def evaluate(rows, scores, pid, dev, test, boots=True):
    have = [r for r in rows if (r["id"], pid) in scores]
    dev_r = [r for r in have if r["id"] in dev]
    test_r = [r for r in have if r["id"] in test]
    if not test_r:
        return None
    yt = [r["label"] for r in test_r]
    st = [scores[(r["id"], pid)] for r in test_r]
    res = {"n_test": len(test_r)}
    res["auroc"] = auroc(yt, st)
    res["R0"] = prf(yt, [1 if v > 0 else 0 for v in st])
    if dev_r:
        yd = [r["label"] for r in dev_r]
        sd = [scores[(r["id"], pid)] for r in dev_r]
        t = best_threshold(yd, sd)
        res["threshold"] = t
        res["R0t"] = prf(yt, [1 if v > t else 0 for v in st])
        if boots:
            res["R0t_ci"] = bootstrap(yt, st, t)
    res["by_type"] = {}
    for c in data.CATEGORIES:
        sub = [r for r in test_r if r["category"] == c]
        if sub:
            y = [r["label"] for r in sub]
            s = [scores[(r["id"], pid)] for r in sub]
            res["by_type"][c] = {"auroc": auroc(y, s), "R0_macro_f1": prf(y, [1 if v > 0 else 0 for v in s])["macro_f1"]}
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("scores")
    ap.add_argument("--csv", default=data.DEFAULT_PATH)
    ap.add_argument("--no-bootstrap", action="store_true")
    args = ap.parse_args()
    rows = data.load(args.csv)
    dev, test = data.split(rows)
    scores = load_scores(args.scores)
    base = prf([r["label"] for r in rows if r["id"] in test], [0] * len(test))
    allm = prf([r["label"] for r in rows if r["id"] in test], [1] * len(test))
    print("test sentences: %d; majority (always literal): acc %.3f macro-F1 %.3f; always metonymic: F1 %.3f"
          % (len(test), base["acc"], base["macro_f1"], allm["f1_meto"]))
    for pid in ("P0", "P1", "S1"):
        res = evaluate(rows, scores, pid, dev, test, boots=not args.no_bootstrap)
        if res is None:
            continue
        print("\n== %s (n_test=%d)  AUROC %.3f" % (pid, res["n_test"], res["auroc"]))
        r0 = res["R0"]
        print("  R0  (threshold 0)   acc %.3f  macro-F1 %.3f  F1(meto) %.3f" % (r0["acc"], r0["macro_f1"], r0["f1_meto"]))
        if "R0t" in res:
            r = res["R0t"]
            line = "  R0t (dev threshold %+.2f) acc %.3f  macro-F1 %.3f  F1(meto) %.3f" % (
                res["threshold"], r["acc"], r["macro_f1"], r["f1_meto"])
            print(line)
            if "R0t_ci" in res:
                ci = res["R0t_ci"]
                print("      95%% CI: macro-F1 [%.3f, %.3f]  AUROC [%.3f, %.3f]" % (
                    ci["macro_f1"][0], ci["macro_f1"][1], ci["auroc"][0], ci["auroc"][1]))
        for c, m in res["by_type"].items():
            print("    %-10s AUROC %.3f  R0 macro-F1 %.3f" % (c, m["auroc"], m["R0_macro_f1"]))


if __name__ == "__main__":
    main()
