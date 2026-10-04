"""Statistical frame lexicon (majority sort per frame from the training partition) as the baseline for typing; evaluated on val and test."""
import json
import os
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
KB = os.path.join(HERE, "..", "data", "kb")
idx = json.load(open(os.path.join(KB, "wimcor_frame_index.json"), encoding="utf-8"))
f2, f1 = defaultdict(Counter), defaultdict(Counter)
glob = Counter()
for sid, (a, b, part, med, coarse) in idx.items():
    if part == "train":
        f2[a][med] += 1
        f1[b][med] += 1
        glob[med] += 1
default = glob.most_common(1)[0][0]


def predict(a, b, min2=2):
    if a in f2 and sum(f2[a].values()) >= min2:
        return f2[a].most_common(1)[0][0], "L2"
    if b in f1:
        return f1[b].most_common(1)[0][0], "L1"
    return default, "none"


MED = ["LOCATION", "INSTITUTE", "TEAM", "ARTIFACT", "EVENT"]
for part in ("val", "test"):
    rows = [(a, b, med) for sid, (a, b, p, med, co) in idx.items() if p == part]
    conf, how = Counter(), Counter()
    for a, b, med in rows:
        pr, h = predict(a, b)
        conf[(med, pr)] += 1
        how[h] += 1
    n = len(rows)
    acc = sum(conf[(m, m)] for m in MED) / n
    print("%s n=%d  accuracy %.3f  backoff use %s" % (part, n, acc, dict(how)))
    for m in MED:
        tp = conf[(m, m)]
        gold = sum(conf[(m, p)] for p in MED)
        pred = sum(conf[(g, m)] for g in MED)
        print("   %-9s gold %6d  recall %.3f  precision %.3f" % (m, gold, tp / max(1, gold), tp / max(1, pred)))
    # clash detection: literal (LOCATION) versus any coerced sort
    tp = sum(v for (g, p), v in conf.items() if g != "LOCATION" and p != "LOCATION")
    fp = sum(v for (g, p), v in conf.items() if g == "LOCATION" and p != "LOCATION")
    fn = sum(v for (g, p), v in conf.items() if g != "LOCATION" and p == "LOCATION")
    print("   clash detection: precision %.3f recall %.3f" % (tp / max(1, tp + fp), tp / max(1, tp + fn)))
