"""Diagnostics that put the LLM scores in context (lexical shortcuts and calibration).

Usage: python experiments/llm/diagnostics.py results/out_qwen25_7b.jsonl
Needs scikit-learn. Reproduces the numbers quoted in results/NOTES.md.
"""
import collections
import json
import os
import sys

import numpy as np
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.linear_model import LogisticRegression
from sklearn.metrics import accuracy_score, f1_score, roc_auc_score
from sklearn.model_selection import GroupKFold

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data
import prompts


def macro(y, p):
    return f1_score(y, p, average="macro")


def main(path):
    rows = data.load()
    dev, test = data.split(rows)
    y = np.array([r["label"] for r in rows])
    d = np.array([r["id"] in dev for r in rows])
    t = ~d
    texts = [r["sentence"] for r in rows]
    cat = np.array([r["category"] for r in rows])
    tgt = np.array([r["category"] + "|" + r["target"].lower() for r in rows])
    docs = np.array([r["doc"] for r in rows])

    raw = {}
    for line in open(path, encoding="utf-8"):
        r = json.loads(line)
        a, b = prompts.ANSWER_TOKENS[r["prompt"]]
        m = prompts.metonymic_token(r["prompt"])
        o = b if m == a else a
        raw[(r["id"], r["prompt"])] = r["lp"][m] - r["lp"][o]
    P = ["P0", "P1", "S1a", "S1b"]
    X = np.array([[raw[(r["id"], p)] for p in P] for r in rows])
    S1 = 0.5 * (X[:, 2] + X[:, 3])

    print("== LLM scores (test): AUROC P0 %.3f  P1 %.3f  S1 %.3f" % (
        roc_auc_score(y[t], X[t, 0]), roc_auc_score(y[t], X[t, 1]), roc_auc_score(y[t], S1[t])))
    print("   mean S1a %+.2f, mean S1b %+.2f (position bias; the average cancels it)" % (X[:, 2].mean(), X[:, 3].mean()))

    # dev-calibrated combiner (supervised calibration on 1000 dev sentences)
    onehot = np.array([[1.0 if c == k else 0.0 for k in data.CATEGORIES] for c in cat])
    feats = np.hstack([X * onehot[:, [k]] for k in range(6)] + [onehot])
    clf = LogisticRegression(C=0.3, max_iter=2000).fit(feats[d], y[d])
    pr = clf.predict_proba(feats[t])[:, 1]
    print("== dev-calibrated combiner of the 4 scores, per-type weights: AUROC %.3f  macro-F1 %.3f"
          % (roc_auc_score(y[t], pr), macro(y[t], (pr > 0.5).astype(int))))

    # lexical shortcuts
    cat_rate = {c: np.mean([r["label"] for r in rows if r["id"] in dev and r["category"] == c]) for c in data.CATEGORIES}
    cnt = collections.defaultdict(lambda: [0, 0])
    for r in rows:
        if r["id"] in dev:
            k = (r["category"], r["target"].lower())
            cnt[k][0] += r["label"]
            cnt[k][1] += 1

    def prior(r, a=2.0):
        m, n = cnt.get((r["category"], r["target"].lower()), [0, 0])
        p = cat_rate[r["category"]]
        return (m + a * p) / (n + a)

    sc = np.array([prior(r) for r in rows])
    print("== target-word prior from dev only (test): AUROC %.3f  macro-F1 %.3f"
          % (roc_auc_score(y[t], sc[t]), macro(y[t], (sc[t] > 0.5).astype(int))))

    def cv(groups, with_target):
        oof = np.zeros(len(rows))
        for tr, te in GroupKFold(5).split(texts, y, groups):
            v = TfidfVectorizer(ngram_range=(1, 2), min_df=2, sublinear_tf=True)
            Xtr, Xte = v.fit_transform([texts[i] for i in tr]), v.transform([texts[i] for i in te])
            if with_target:
                from scipy.sparse import hstack
                v2 = TfidfVectorizer(analyzer=lambda s: [s])
                Xtr, Xte = hstack([Xtr, v2.fit_transform([tgt[i] for i in tr])]), hstack([Xte, v2.transform([tgt[i] for i in te])])
            m = LogisticRegression(C=3, max_iter=3000).fit(Xtr, y[tr])
            oof[te] = m.predict_proba(Xte)[:, 1]
        return oof

    for name, groups, wt in (("TF-IDF + target one-hot, grouped by document (in-distribution)", docs, True),
                             ("TF-IDF sentence only, grouped by TARGET word (unseen words)", tgt, False)):
        oof = cv(groups, wt)
        p = (oof > 0.5).astype(int)
        print("== %s: AUROC %.3f  acc %.3f  macro-F1 %.3f" % (name, roc_auc_score(y, oof), accuracy_score(y, p), macro(y, p)))
        if not wt:
            for c in data.CATEGORIES:
                m = cat == c
                print("     %-10s TF-IDF(unseen target) %.3f   Qwen S1 %.3f" % (c, roc_auc_score(y[m], oof[m]), roc_auc_score(y[m], S1[m])))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "results/out_qwen25_7b.jsonl")
