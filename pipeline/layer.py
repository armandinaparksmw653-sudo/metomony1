"""E3: the candidate layer. Parse -> type clash -> space of readings from the knowledge base -> certificate.

    python pipeline/layer.py [--parse results/colab_run3/parse_relocar.jsonl]

For a ReLocaR sentence with a linked place (constant = index of the place in the snapshot) and the parse of the neural
step (which kind of entity the governing predicate requires: PLACE, POLITY, TEAM or PEOPLE):
  * no clash   : the required sort is Place, the reading is literal (empty route);
  * clash      : the readings are the edges Place -> required sort that are *defined for this place in the snapshot*
                 (the place has at least one related element); each reading carries its referents;
  * no reading : a clash with an empty space, the formal layer reports that the knowledge base offers nothing.
The choice among several readings is not made here (E4); `choose` takes the first admissible edge in lexicon order.
"""
import argparse
import json
import os
import sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lexicon  # noqa: E402
import relocar  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
LEX = os.path.join(HERE, "..", "lexicon", "toponym_v1.json")
SORT = {"PLACE": "Place", "POLITY": "Polity", "TEAM": "Team", "PEOPLE": "People"}
SIZE_KEY = {"Polity": "polities", "Team": "teams"}


class Layer:
    def __init__(self):
        self.lx = lexicon.load(LEX)
        self.snap = json.load(open(os.path.join(KB, "snapshot.json"), encoding="utf-8"))
        self.chosen = json.load(open(os.path.join(KB, "chosen.json"), encoding="utf-8"))
        self.pidx = {q: i for i, q in enumerate(self.snap["places"])}
        self.by_place = {e: {} for e in self.snap["rel"]}
        for e, pairs in self.snap["rel"].items():
            for i, j in pairs:
                self.by_place[e].setdefault(i, []).append(j)
        self.n = len(self.snap["places"])

    def size(self, sort):
        return self.n if sort in ("Place", "People") else len(self.snap[SIZE_KEY[sort]])

    def readings(self, place, sort):
        """Admissible readings of a place coerced to `sort`: list of (edge name, referents)."""
        if sort == "Place":
            return [("literal", [place])]
        out = []
        for e in self.lx.edges:
            if e["src"] == "Place" and e["tgt"] == sort and self.by_place[e["name"]].get(place):
                out.append((e["name"], self.by_place[e["name"]][place]))
        return out

    def certificate(self, place, sort, edge, referent):
        route = [] if edge == "literal" else [self.lx.edge_id[edge]]
        return {"mode": "resolve", "pred": self.lx.pred_id["req" + sort], "const": place, "route": route, "refs": [referent]}

    def controls_info(self, place, sort, edge, referent):
        """Material for corrupted certificates: a referent not related to the place, a place without that institution."""
        info = {"n_places": self.n}
        related = set(self.by_place.get(edge, {}).get(place, [])) if edge != "literal" else {place}
        info["wrong_ref"] = next((j for j in range(self.size(sort)) if j not in related), None)
        if edge != "literal":
            info["empty_place"] = next((i for i in range(self.n) if not self.by_place[edge].get(i)), None)
        return info


def analyse(layer, rows, parses):
    items, stats = [], Counter()
    for r in rows:
        q = layer.chosen.get(r["name"])
        p = parses.get(r["id"])
        if not q or r["label"] == "mixed":
            stats[(r["label"], "skipped")] += 1
            continue
        if not p:
            stats[(r["label"], "parse failed")] += 1
            continue
        place = layer.pidx[q]
        sort = SORT[p["requires"]]
        rd = layer.readings(place, sort)
        clash = sort != "Place"
        state = "no clash" if not clash else ("space %d" % len(rd) if rd else "no reading")
        stats[(r["label"], state)] += 1
        it = {"id": r["id"], "label": r["label"], "name": r["name"], "qid": q, "required": sort, "clash": clash,
              "readings": [(e, len(ref)) for e, ref in rd], "predicate": p.get("predicate")}
        if rd:
            edge, refs = rd[0]
            it["cert"] = layer.certificate(place, sort, edge, refs[0])
            it["ctl"] = layer.controls_info(place, sort, edge, refs[0])
            it["edge"] = edge
        items.append(it)
    return items, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--parse", default=os.path.join(HERE, "..", "results", "colab_run3", "parse_relocar.jsonl"))
    ap.add_argument("--out", default=os.path.join(HERE, "..", "results", "toponym_items.jsonl"))
    a = ap.parse_args()
    layer = Layer()
    rows = relocar.load("train") + relocar.load("test")
    parses = {}
    for l in open(a.parse, encoding="utf-8"):
        j = json.loads(l)
        parses[j["id"]] = j["parsed"]
    items, stats = analyse(layer, rows, parses)
    for lab in ("literal", "metonymic"):
        print(lab, {k[1]: v for k, v in sorted(stats.items()) if k[0] == lab})
    with open(a.out, "w", encoding="utf-8") as f:
        for it in items:
            f.write(json.dumps(it) + "\n")
    cl = [i for i in items if i["clash"]]
    print("sentences analysed %d; with clash %d; certificates %d" % (len(items), len(cl), sum(1 for i in items if "cert" in i)))
    print("readings per clash:", Counter(len(i["readings"]) for i in cl))
    print("edge sets of the spaces:", Counter(tuple(e for e, _ in i["readings"]) for i in cl).most_common(8))


if __name__ == "__main__":
    main()
