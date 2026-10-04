"""Typing of WiMCor sentences by the frame lexicon: language model (Qwen2.5-7B, no labels seen), statistics of the training partition, and their combination.

    python pipeline/frame_lexicon_eval.py [--scores results/colab_run3/frame_scores.jsonl]

Frame -> sort of the mention: the two-token frame if it was annotated (at least 5 occurrences), else the one-token frame.
LLM sorts are mapped PLACE -> LOCATION, INSTITUTION -> INSTITUTE, ANY -> LOCATION (nothing requires a coercion).
Combination: log p_LLM + lam * log p_train(smoothed), lam chosen on val and reported on test.
"""
import argparse
import json
import math
import os
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
KB = os.path.join(HERE, "..", "data", "kb")
MED = ["LOCATION", "INSTITUTE", "TEAM", "ARTIFACT", "EVENT"]
MAP = {"PLACE": "LOCATION", "INSTITUTION": "INSTITUTE", "TEAM": "TEAM", "EVENT": "EVENT", "ARTIFACT": "ARTIFACT", "ANY": "LOCATION"}


def load_llm(path):
    llm = {}
    for line in open(path, encoding="utf-8"):
        j = json.loads(line)
        d = defaultdict(float)
        m = defaultdict(list)
        for s, lp in zip(j["sorts"], j["lp"]):
            m[MAP[s]].append(math.exp(lp))
        tot = sum(sum(v) for v in m.values())
        llm[(j["level"], j["frame"])] = {k: sum(v) / tot for k, v in m.items()}
    return llm


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scores", default=os.path.join(HERE, "..", "results", "colab_run3", "frame_scores.jsonl"))
    a = ap.parse_args()
    idx = json.load(open(os.path.join(KB, "wimcor_frame_index.json"), encoding="utf-8"))
    llm = load_llm(a.scores)
    st2, st1, glob = defaultdict(Counter), defaultdict(Counter), Counter()
    for sid, (f2, f1, part, med, co) in idx.items():
        if part == "train":
            st2[f2][med] += 1
            st1[f1][med] += 1
            glob[med] += 1
    gt = sum(glob.values())
    prior = {m: glob[m] / gt for m in MED}

    def stat(f2, f1):
        c = st2.get(f2)
        if c and sum(c.values()) >= 2:
            tot = sum(c.values())
            return {m: (c[m] + 0.5 * prior[m]) / (tot + 0.5) for m in MED}
        c = st1.get(f1)
        if c:
            tot = sum(c.values())
            return {m: (c[m] + 0.5 * prior[m]) / (tot + 0.5) for m in MED}
        return dict(prior)

    def llm_dist(f2, f1):
        if (2, f2) in llm:
            return llm[(2, f2)], "L2"
        if (1, f1) in llm:
            return llm[(1, f1)], "L1"
        return None, "none"

    def predict(f2, f1, mode, lam):
        ld, how = llm_dist(f2, f1)
        sd = stat(f2, f1)
        if mode == "stat" or ld is None:
            return max(MED, key=lambda m: sd[m])
        if mode == "llm":
            return max(MED, key=lambda m: ld.get(m, 1e-9))
        return max(MED, key=lambda m: math.log(ld.get(m, 1e-9)) + lam * math.log(sd[m]))

    rows = {p: [(f2, f1, med) for sid, (f2, f1, pp, med, co) in idx.items() if pp == p] for p in ("val", "test")}

    def evaluate(part, mode, lam=1.0, verbose=False):
        conf = Counter()
        for f2, f1, med in rows[part]:
            conf[(med, predict(f2, f1, mode, lam))] += 1
        n = len(rows[part])
        acc = sum(conf[(m, m)] for m in MED) / n
        rec = {m: conf[(m, m)] / max(1, sum(conf[(m, p)] for p in MED)) for m in MED}
        pre = {m: conf[(m, m)] / max(1, sum(conf[(g, m)] for g in MED)) for m in MED}
        macro = sum(rec.values()) / len(MED)
        tp = sum(v for (g, p), v in conf.items() if g != "LOCATION" and p != "LOCATION")
        fp = sum(v for (g, p), v in conf.items() if g == "LOCATION" and p != "LOCATION")
        fn = sum(v for (g, p), v in conf.items() if g != "LOCATION" and p == "LOCATION")
        if verbose:
            print("%-14s %s: acc %.3f macro-recall %.3f | clash precision %.3f recall %.3f" % (mode + ("" if mode != "combo" else " lam=%.2f" % lam), part, acc, macro, tp / max(1, tp + fp), tp / max(1, tp + fn)))
            print("     recall   " + "  ".join("%s %.2f" % (m[:4], rec[m]) for m in MED))
            print("     precision" + "  ".join("%s %.2f" % (m[:4], pre[m]) for m in MED))
        return macro

    for part in ("val", "test"):
        evaluate(part, "stat", verbose=True)
        evaluate(part, "llm", verbose=True)
    best = max([0.0, 0.25, 0.5, 1.0, 2.0, 4.0], key=lambda l: evaluate("val", "combo", l))
    print("best lam on val (macro-recall):", best)
    for part in ("val", "test"):
        evaluate(part, "combo", best, verbose=True)
    cov = Counter()
    for f2, f1, med in rows["test"]:
        cov[llm_dist(f2, f1)[1]] += 1
    print("LLM lexicon level used on test:", dict(cov))


if __name__ == "__main__":
    main()
