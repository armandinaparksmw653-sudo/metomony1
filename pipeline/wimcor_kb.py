"""Knowledge base for WiMCor from Wikidata.

    python pipeline/wimcor_kb.py titles      # Wikipedia titles -> QIDs (batched), cached in data/kb/wimcor_titles.json
    python pipeline/wimcor_kb.py relations   # direct Wikidata relations between the place and the referent of every pair

Step "relations" answers the feasibility question: how often is the gold referent reachable from the place in Wikidata, and by which
properties. Everything is cached in data/kb/ (Wikidata is CC0), so later stages need no network.
"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import wimcor  # noqa: E402
import wikidata as wd  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
TITLES = os.path.join(KB, "wimcor_titles.json")
REL = os.path.join(KB, "wimcor_relations.json")


def all_titles():
    t = set()
    for p in wimcor.pairs():
        t.add(p["place"])
        t.add(p["referent"])
    for r in wimcor.load():
        t.add(r["fine"])
    return sorted(t)


def titles():
    os.makedirs(KB, exist_ok=True)
    cache = json.load(open(TITLES, encoding="utf-8")) if os.path.exists(TITLES) else {}
    todo = [t for t in all_titles() if t not in cache]
    print(len(todo), "titles to resolve", flush=True)
    for i in range(0, len(todo), 50):
        batch = todo[i:i + 50]
        r = wd.call({"action": "wbgetentities", "sites": "enwiki", "titles": "|".join(batch), "props": "sitelinks|labels", "languages": "en", "sitefilter": "enwiki"})
        found = {}
        for q, e in ((r or {}).get("entities") or {}).items():
            if q.startswith("Q"):
                found[e["sitelinks"]["enwiki"]["title"]] = q
        norm = {n["from"]: n["to"] for n in ((r or {}).get("normalized") or [])} if isinstance(r, dict) and "normalized" in r else {}
        for t in batch:
            cache[t] = found.get(norm.get(t, t))
        if r is not None and (i // 50) % 10 == 0:
            json.dump(cache, open(TITLES, "w", encoding="utf-8"), ensure_ascii=False)
            print(i, len(todo), flush=True)
        time.sleep(0.3)
    json.dump(cache, open(TITLES, "w", encoding="utf-8"), ensure_ascii=False)
    print("resolved", sum(1 for v in cache.values() if v), "of", len(cache))


def relations():
    q = json.load(open(TITLES, encoding="utf-8"))
    used = {r["fine"] for r in wimcor.load() if r["coarse"] == "met"}
    ps = [p for p in wimcor.pairs() if p["referent"] in used and q.get(p["place"]) and q.get(p["referent"])]
    print(len(ps), "pairs whose referent occurs in the corpus and both titles resolve", flush=True)
    uniq = sorted({(q[p["place"]], q[p["referent"]]) for p in ps})
    out = json.load(open(REL, encoding="utf-8")) if os.path.exists(REL) else {}
    todo = [u for u in uniq if "%s|%s" % u not in out]
    for i in range(0, len(todo), 80):
        batch = todo[i:i + 80]
        vals = " ".join("(wd:%s wd:%s)" % u for u in batch)
        fwd = wd.sparql("SELECT ?a ?b ?p WHERE { VALUES (?a ?b) { %s } ?a ?p ?b . FILTER(STRSTARTS(STR(?p), 'http://www.wikidata.org/prop/direct/')) }" % vals)
        bwd = wd.sparql("SELECT ?a ?b ?p WHERE { VALUES (?a ?b) { %s } ?b ?p ?a . FILTER(STRSTARTS(STR(?p), 'http://www.wikidata.org/prop/direct/')) }" % vals)
        for u in batch:
            out["%s|%s" % u] = {"fwd": [], "bwd": []}
        for key, res in (("fwd", fwd), ("bwd", bwd)):
            for b in res or []:
                a, c = b["a"]["value"].rsplit("/", 1)[1], b["b"]["value"].rsplit("/", 1)[1]
                out["%s|%s" % (a, c)][key].append(b["p"]["value"].rsplit("/", 1)[1])
        if (i // 80) % 5 == 0:
            json.dump(out, open(REL, "w", encoding="utf-8"))
            print(i, len(todo), flush=True)
        time.sleep(1)
    json.dump(out, open(REL, "w", encoding="utf-8"))
    byt = {}
    for p in ps:
        r = out.get("%s|%s" % (q[p["place"]], q[p["referent"]]))
        byt.setdefault(p["medium"], []).append(r)
    for m, rs in byt.items():
        hit = [r for r in rs if r and (r["fwd"] or r["bwd"])]
        c = Counter(("<-" if k == "bwd" else "->") + x for r in hit for k in ("fwd", "bwd") for x in set(r[k]))
        print("%-10s pairs %5d  with a direct relation %5d (%.0f%%)  top: %s" % (m, len(rs), len(hit), 100 * len(hit) / max(1, len(rs)), c.most_common(6)))


if __name__ == "__main__":
    {"titles": titles, "relations": relations}[sys.argv[1]]()
