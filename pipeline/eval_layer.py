"""Decisions of the toponym pipeline against the ReLocaR gold labels (needs results/toponym_items.jsonl from layer.py)."""
import json
import os
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
it = [json.loads(l) for l in open(os.path.join(HERE, "..", "results", "toponym_items.jsonl"), encoding="utf-8")]


def ev(name, f):
    tp = sum(1 for i in it if f(i) and i["label"] == "metonymic")
    fp = sum(1 for i in it if f(i) and i["label"] == "literal")
    fn = sum(1 for i in it if not f(i) and i["label"] == "metonymic")
    tn = sum(1 for i in it if not f(i) and i["label"] == "literal")
    p, r = tp / max(1, tp + fp), tp / max(1, tp + fn)
    n0, r0 = tn / max(1, tn + fn), tn / max(1, tn + fp)
    f1, f0 = 2 * p * r / max(1e-9, p + r), 2 * n0 * r0 / max(1e-9, n0 + r0)
    print("%-32s acc %.3f  prec %.3f  rec %.3f  macro-F1 %.3f  (n=%d)" % (name, (tp + tn) / len(it), p, r, (f1 + f0) / 2, len(it)))


ev("metonymic iff type clash", lambda i: i["clash"])
ev("clash and KB space nonempty", lambda i: i["clash"] and bool(i["readings"]))
cl = [i for i in it if i["clash"]]
for lab in ("metonymic", "literal"):
    g = [i for i in cl if i["label"] == lab]
    print("%-9s clashes: %d, KB offers a reading for %d (%.0f%%)" % (lab, len(g), sum(1 for i in g if i["readings"]), 100 * sum(1 for i in g if i["readings"]) / max(1, len(g))))
print("by required sort and KB support:", sorted(Counter((i["required"], bool(i["readings"])) for i in cl).items()))
