"""ConMeC loading and a deterministic split.

ConMeC (Ghosh and Jiang 2025, Apache-2.0): 6000 Wikipedia sentences, six metonymy types (1000 each),
binary label LITERAL / METONYMIC. Source: https://github.com/SaptGhosh/ConMeC

The data is downloaded from the original repository (not copied into this one).
The split is by document, so sentences from one article never fall into both dev and test.
Dev is used for few-shot demonstrations and for choosing a decision threshold; test is never used for either.
"""
import csv
import os
import random
import urllib.request

URL = "https://raw.githubusercontent.com/SaptGhosh/ConMeC/main/DATASET.csv"
DEFAULT_PATH = os.path.join(os.path.dirname(__file__), "..", "..", "data", "raw", "conmec.csv")

CATEGORIES = ["CONTAINER", "PRODUCER", "PRODUCT", "LOCATION", "CAUSER", "POSSESSED"]


def load(path=DEFAULT_PATH):
    path = os.path.abspath(path)
    if not os.path.exists(path):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        urllib.request.urlretrieve(URL, path)
    rows = []
    with open(path, encoding="utf-8", newline="") as f:
        for i, r in enumerate(csv.DictReader(f)):
            rows.append({
                "id": i,
                "label": 1 if r["Label"] == "METONYMIC" else 0,
                "category": r["Category"],
                "target": r["Target Word (Noun)"],
                "sentence": r["Sentence"],
                "prev": r["Sentence T-1"],
                "doc": r["Document URL"],
            })
    return rows


def split(rows, dev_size=1000, seed=13):
    """Document-grouped split. Returns (dev_ids, test_ids) as sets of row ids."""
    docs = {}
    for r in rows:
        docs.setdefault(r["doc"], []).append(r["id"])
    keys = sorted(docs)
    random.Random(seed).shuffle(keys)
    dev = set()
    for k in keys:
        if len(dev) >= dev_size:
            break
        dev.update(docs[k])
    test = {r["id"] for r in rows} - dev
    return dev, test


if __name__ == "__main__":
    rows = load()
    dev, test = split(rows)
    print(len(rows), "rows;", len(dev), "dev;", len(test), "test")
    for name, ids in (("dev", dev), ("test", test)):
        sel = [r for r in rows if r["id"] in ids]
        m = sum(r["label"] for r in sel)
        print(name, "metonymic share %.3f" % (m / len(sel)))
