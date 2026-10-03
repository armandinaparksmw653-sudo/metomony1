"""E4 input: for each ReLocaR sentence the candidate space built by the formal layer.

    python pipeline/e4_input.py     # writes results/e4_input.jsonl (not tracked) and prints statistics

Space = the literal reading plus every edge of the lexicon that is defined for the place in the snapshot (admissible for the
place whatever the parse says). Scores for the whole space are computed once by the neural step; the restriction by the parse
(only readings of the sort the predicate requires) is applied afterwards in the pipeline.
"""
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import layer  # noqa: E402
import relocar  # noqa: E402

TEXT = {
    "literal": "the geographic place itself (its land, location or territory)",
    "exec": "the executive government of the place (its leaders and ministries)",
    "legis": "the legislature or parliament of the place",
    "team": "a sports team that represents the place",
    "pop": "the people who live in the place",
}


def main():
    lay = layer.Layer()
    rows = relocar.load("train") + relocar.load("test")
    out, sizes = [], Counter()
    for r in rows:
        q = lay.chosen.get(r["name"])
        if not q or r["label"] == "mixed":
            continue
        place = lay.pidx[q]
        cands = [{"id": "literal", "text": TEXT["literal"]}]
        for e in lay.lx.edges:
            if lay.by_place[e["name"]].get(place):
                cands.append({"id": e["name"], "text": TEXT[e["name"]]})
        sizes[len(cands)] += 1
        out.append({"id": r["id"], "name": r["name"], "sentence": r["sentence"], "cands": cands})
    path = os.path.join(HERE, "..", "results", "e4_input.jsonl")
    with open(path, "w", encoding="utf-8") as f:
        for o in out:
            f.write(json.dumps(o, ensure_ascii=False) + "\n")
    print(len(out), "sentences; candidates per sentence:", sorted(sizes.items()))


if __name__ == "__main__":
    main()
