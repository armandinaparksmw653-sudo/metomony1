"""Lexicon: the single source of truth for sorts, coercion edges, declared equivalences, constants, predicates.

The JSON file is loaded and validated here; the Agda modules are generated from it (gen_agda.py), so the
Python side and the verified side cannot drift apart. Identifiers (edge names as numbers, etc.) are the
positions in the JSON lists and are what certificates carry across to Agda.
"""
import json
import os
from dataclasses import dataclass, field

HERE = os.path.dirname(os.path.abspath(__file__))
DEFAULT = os.path.join(HERE, "..", "lexicon", "conmec_v1.json")


@dataclass
class Lexicon:
    name: str
    sorts: list
    edges: list            # dicts with name, src, tgt, type, literal, reading
    rules: list            # dicts with name, src, tgt, lhs (edge names), rhs (edge names)
    constants: list        # dicts with name, sort
    predicates: list       # dicts with name, sig (list of sorts)
    edge_id: dict = field(default_factory=dict)
    pred_id: dict = field(default_factory=dict)
    const_id: dict = field(default_factory=dict)
    numeric_sort: str = None

    # -- candidates for a sentence about a noun whose literal sort is known (here via the ConMeC type)
    def literal_sort(self, type_name):
        return next(e["src"] for e in self.edges if e["type"] == type_name)

    def edges_from(self, sort):
        return [e for e in self.edges if e["src"] == sort]

    def candidates(self, type_name):
        """Readings licensed by the lexicon for a noun of this type: the literal one and one per edge."""
        s = self.literal_sort(type_name)
        out = [{"name": "literal", "sort": s, "route": [], "text": next(e["literal"] for e in self.edges if e["type"] == type_name)}]
        for e in self.edges_from(s):
            out.append({"name": e["name"], "sort": e["tgt"], "route": [e["name"]], "text": e["reading"]})
        return out

    def const_of_sort(self, sort):
        return next(c["name"] for c in self.constants if c["sort"] == sort)

    def pred_of_sort(self, sort):
        return next(p["name"] for p in self.predicates if p["sig"] == [sort])


def load(path=DEFAULT):
    d = json.load(open(path, encoding="utf-8"))
    consts = d["constants"]
    numeric = consts.get("numeric") if isinstance(consts, dict) else None
    lex = Lexicon(d["name"], d["sorts"], d["edges"], d.get("rules", []), [] if numeric else consts, d["predicates"])
    lex.numeric_sort = numeric     # constants are numbered by the knowledge base, not listed here
    validate(lex)
    lex.edge_id = {e["name"]: i for i, e in enumerate(lex.edges)}
    lex.pred_id = {p["name"]: i for i, p in enumerate(lex.predicates)}
    lex.const_id = {c["name"]: i for i, c in enumerate(lex.constants)}
    return lex


def validate(lex):
    sorts = set(lex.sorts)
    assert len(sorts) == len(lex.sorts), "duplicate sorts"
    for kind, items in (("edge", lex.edges), ("constant", lex.constants), ("predicate", lex.predicates), ("rule", lex.rules)):
        names = [x["name"] for x in items]
        assert len(set(names)) == len(names), "duplicate %s names" % kind
    for e in lex.edges:
        assert e["src"] in sorts and e["tgt"] in sorts, "edge %s has an unknown sort" % e["name"]
    for c in lex.constants:
        assert c["sort"] in sorts, "constant %s has an unknown sort" % c["name"]
    for p in lex.predicates:
        assert all(s in sorts for s in p["sig"]), "predicate %s has an unknown sort" % p["name"]
    edge = {e["name"]: e for e in lex.edges}
    for r in lex.rules:
        for side in ("lhs", "rhs"):
            assert all(n in edge for n in r[side]), "rule %s uses an unknown edge" % r["name"]
        assert len(r["lhs"]) > len(r["rhs"]), "rule %s must shorten the route" % r["name"]
        for side in ("lhs", "rhs"):
            cur = r["src"]
            for n in r[side]:
                assert edge[n]["src"] == cur, "rule %s: %s is not a path" % (r["name"], side)
                cur = edge[n]["tgt"]
            assert cur == r["tgt"], "rule %s: %s ends at the wrong sort" % (r["name"], side)
    # every literal sort used by a type must have a constant and every sort a unary predicate
    for e in lex.edges:
        assert lex.numeric_sort == e["src"] or any(c["sort"] == e["src"] for c in lex.constants), "no constant of sort %s" % e["src"]
    for s in lex.sorts:
        assert any(p["sig"] == [s] for p in lex.predicates), "no unary predicate on sort %s" % s


if __name__ == "__main__":
    lx = load()
    print(lx.name, "|", len(lx.sorts), "sorts,", len(lx.edges), "edges,", len(lx.rules), "rules")
    for t in ("CONTAINER", "LOCATION"):
        print(t, [c["name"] for c in lx.candidates(t)])
