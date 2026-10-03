"""Candidate spaces for WiMCor from Wikidata.

    python pipeline/wimcor_space.py sample   # stratified evaluation sample of the test partition, with the place of every sentence
    python pipeline/wimcor_space.py cands    # entities of every sort related to those places in Wikidata (cached)
    python pipeline/wimcor_space.py report   # reachability of the gold referent and sizes of the spaces

Place linking is an oracle: for a literal sentence the place is the page of the literal label, for a metonymic one the place page of
the metonymic pair the referent was harvested from (best match to the surface form when there are several). Place linking is not
what is evaluated here.

Sorts and the Wikidata classes (with all subclasses) that define them; the relation from a place to an element of the sort is
located-in (P131), headquarters location (P159) or location (P276) of the element pointing at the place.
"""
import json
import os
import random
import sys
import time
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import wimcor  # noqa: E402
import wikidata as wd  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
ROOTS = {
    "Institute": ["Q2385804", "Q31855"],                       # educational institution, research institute
    "Team": ["Q12973014", "Q847017"],                          # sports team, sports club
    "Event": ["Q178561", "Q198", "Q188055", "Q132241", "Q124734"],   # battle, war, siege, festival, rebellion
    "Artifact": ["Q41176", "Q245016", "Q1248784", "Q22698", "Q473972", "Q719456", "Q33506", "Q839954"],
    # building, military base, airport, park, protected area, station, museum, archaeological site
}
STRATA = {"LOCATION": 1200, "INSTITUTE": 800, "TEAM": 500, "ARTIFACT": 500, "EVENT": 200}
SORT_OF = {"INSTITUTE": "Institute", "TEAM": "Team", "ARTIFACT": "Artifact", "EVENT": "Event", "LOCATION": "Place"}


def titles():
    return json.load(open(os.path.join(KB, "wimcor_titles.json"), encoding="utf-8"))


def sample():
    q = titles()
    pairs = defaultdict(list)
    for p in wimcor.pairs():
        pairs[p["referent"]].append(p)
    rows = wimcor.load("test")
    rng = random.Random(11)
    out = []
    for medium, n in STRATA.items():
        pool = [r for r in rows if r["medium"] == medium]
        rng.shuffle(pool)
        for r in pool:
            if len([o for o in out if o["medium"] == medium]) >= n:
                break
            if r["coarse"] == "lit":
                place, referent = r["fine"], None
            else:
                cands = pairs.get(r["fine"], [])
                if not cands:
                    continue
                exact = [p for p in cands if p["place"] == r["surface"] or p["place"].split(",")[0] == r["surface"]]
                place, referent = (exact or cands)[0]["place"], r["fine"]
            if not q.get(place) or (referent and not q.get(referent)):
                continue
            out.append({"id": r["id"], "medium": medium, "coarse": r["coarse"], "surface": r["surface"], "place": place, "place_qid": q[place],
                        "referent": referent, "referent_qid": q.get(referent) if referent else None,
                        "sentence": wimcor.sentence(r), "left": r["left"], "right": r["right"]})
    json.dump(out, open(os.path.join(KB, "wimcor_sample.json"), "w", encoding="utf-8"), ensure_ascii=False)
    print(len(out), "sentences;", Counter(o["medium"] for o in out), "; places", len({o["place_qid"] for o in out}))


def cands():
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    places = sorted({o["place_qid"] for o in sm})
    path = os.path.join(KB, "wimcor_cands.json")
    out = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else {}
    B = int(os.environ.get("BATCH", "10"))
    for sort, roots in ROOTS.items():
        for i in range(0, len(places), B):
            batch = [p for p in places[i:i + B] if sort not in out.get(p, {})]
            if not batch:
                continue
            q = """SELECT DISTINCT ?p ?x WHERE { VALUES ?p { %s } VALUES ?r { %s }
              { ?x wdt:P159 ?p } UNION { ?x wdt:P131 ?p } UNION { ?x wdt:P276 ?p }
              ?x wdt:P31 ?c . ?c wdt:P279* ?r . } LIMIT 5000""" % (" ".join("wd:" + p for p in batch), " ".join("wd:" + r for r in roots))
            res = wd.sparql(q)
            if res is None:
                print("failed batch", sort, i, flush=True)
                continue
            for p in batch:
                out.setdefault(p, {})[sort] = []
            for b in res:
                out[b["p"]["value"].rsplit("/", 1)[1]][sort].append(b["x"]["value"].rsplit("/", 1)[1])
            if (i // B) % 5 == 0:
                json.dump(out, open(path, "w", encoding="utf-8"))
                print(sort, i, len(places), flush=True)
            time.sleep(0.5)
    json.dump(out, open(path, "w", encoding="utf-8"))
    print("done")


def cands_named():
    """Same, but the element must carry the surface form of the mention in its English label (name compatibility), applied in the query."""
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    keys = sorted({(o["place_qid"], o["surface"].lower()) for o in sm})
    path = os.path.join(KB, "wimcor_cands_named.json")
    out = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else {}
    B = int(os.environ.get("BATCH", "8"))
    for sort, roots in ROOTS.items():
        for i in range(0, len(keys), B):
            batch = [k for k in keys[i:i + B] if sort not in out.get("%s|%s" % k, {})]
            if not batch:
                continue
            vals = " ".join('(wd:%s "%s")' % (p, n.replace("\\", " ").replace('"', " ")) for p, n in batch)
            q = """SELECT DISTINCT ?p ?n ?x ?l WHERE { VALUES (?p ?n) { %s } VALUES ?r { %s }
              { ?x wdt:P159 ?p } UNION { ?x wdt:P131 ?p } UNION { ?x wdt:P276 ?p }
              ?x rdfs:label ?l . FILTER(LANG(?l) = "en" && CONTAINS(LCASE(STR(?l)), ?n))
              ?x wdt:P31 ?c . ?c wdt:P279* ?r . } LIMIT 5000""" % (vals, " ".join("wd:" + r for r in roots))
            res = wd.sparql(q)
            if res is None:
                print("failed batch", sort, i, flush=True)
                continue
            for k in batch:
                out.setdefault("%s|%s" % k, {})[sort] = {}
            for b in res:
                key = "%s|%s" % (b["p"]["value"].rsplit("/", 1)[1], b["n"]["value"])
                out[key][sort][b["x"]["value"].rsplit("/", 1)[1]] = b["l"]["value"]
            if (i // B) % 10 == 0:
                json.dump(out, open(path, "w", encoding="utf-8"), ensure_ascii=False)
                print(sort, i, len(keys), flush=True)
            time.sleep(0.5)
    json.dump(out, open(path, "w", encoding="utf-8"), ensure_ascii=False)
    print("done")


def cands_search():
    """Elements whose label or alias matches the surface form (Wikidata entity search), of the classes of every sort.
    The relation of the lexicon is name compatibility; `loc` records whether the element is also located at the place."""
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    keys = sorted({(o["place_qid"], o["surface"]) for o in sm})
    path = os.path.join(KB, "wimcor_cands_search.json")
    out = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else {}
    root_sort = {r: s for s, rs in ROOTS.items() for r in rs}
    for n, (p, surf) in enumerate(keys):
        key = "%s|%s" % (p, surf)
        if key in out:
            continue
        name = surf.replace("\\", " ").replace('"', " ")
        q = """SELECT DISTINCT ?x ?xl ?r ?loc WHERE {
          SERVICE wikibase:mwapi { bd:serviceParam wikibase:api "EntitySearch"; wikibase:endpoint "www.wikidata.org";
             mwapi:search "%s"; mwapi:language "en"; mwapi:limit "500" . ?x wikibase:apiOutputItem mwapi:item . }
          VALUES ?r { %s } ?x wdt:P31 ?c . ?c wdt:P279* ?r . ?x rdfs:label ?xl FILTER(LANG(?xl) = "en")
          BIND(EXISTS { { ?x wdt:P159 wd:%s } UNION { ?x wdt:P131 wd:%s } UNION { ?x wdt:P276 wd:%s } } AS ?loc) } LIMIT 2000""" % (
            name, " ".join("wd:" + r for r in root_sort), p, p, p)
        res = wd.sparql(q)
        if res is None:
            print("failed", key, flush=True)
            continue
        d = {}
        for b in res:
            x = b["x"]["value"].rsplit("/", 1)[1]
            r = b["r"]["value"].rsplit("/", 1)[1]
            e = d.setdefault(root_sort[r], {}).setdefault(x, {"label": b["xl"]["value"], "loc": False})
            e["loc"] = e["loc"] or b["loc"]["value"] == "true"
        out[key] = d
        if n % 25 == 0:
            json.dump(out, open(path, "w", encoding="utf-8"), ensure_ascii=False)
            print(n, len(keys), flush=True)
        time.sleep(0.3)
    json.dump(out, open(path, "w", encoding="utf-8"), ensure_ascii=False)
    print("done")


def report_search():
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    cd = json.load(open(os.path.join(KB, "wimcor_cands_search.json"), encoding="utf-8"))
    nm = json.load(open(os.path.join(KB, "wimcor_cands_named.json"), encoding="utf-8"))
    hit, hit2, tot, sizes = Counter(), Counter(), Counter(), defaultdict(list)
    for o in sm:
        sp = cd.get("%s|%s" % (o["place_qid"], o["surface"]), {})
        np_ = nm.get("%s|%s" % (o["place_qid"], o["surface"].lower()), {})
        union = {s: set(sp.get(s, {})) | set(np_.get(s, {})) for s in ROOTS}
        if o["coarse"] == "met":
            sort = SORT_OF[o["medium"]]
            tot[sort] += 1
            hit[sort] += o["referent_qid"] in sp.get(sort, {})
            hit2[sort] += o["referent_qid"] in union[sort]
        sizes[o["medium"]].append(sum(len(v) for v in union.values()))
    for s in tot:
        print("%-10s gold in search space: %d/%d (%.0f%%); in search or located-name space: %d/%d (%.0f%%)" % (s, hit[s], tot[s], 100 * hit[s] / tot[s], hit2[s], tot[s], 100 * hit2[s] / tot[s]))
    for m, v in sizes.items():
        v.sort()
        print("%-10s union space size: median %d, 90th pct %d, max %d" % (m, v[len(v) // 2], v[int(len(v) * .9)], v[-1]))


def report_named():
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    cd = json.load(open(os.path.join(KB, "wimcor_cands_named.json"), encoding="utf-8"))
    hit, tot, sizes = Counter(), Counter(), defaultdict(list)
    for o in sm:
        sp = cd.get("%s|%s" % (o["place_qid"], o["surface"].lower()), {})
        if o["coarse"] == "met":
            sort = SORT_OF[o["medium"]]
            tot[sort] += 1
            if o["referent_qid"] in sp.get(sort, {}):
                hit[sort] += 1
        sizes[o["medium"]].append(sum(len(v) for v in sp.values()))
    for s in tot:
        print("%-10s gold referent in the space of its sort: %d/%d (%.0f%%)" % (s, hit[s], tot[s], 100 * hit[s] / tot[s]))
    for m, v in sizes.items():
        v.sort()
        print("%-10s space size (all sorts): median %d, 90th pct %d, max %d" % (m, v[len(v) // 2], v[int(len(v) * .9)], v[-1]))


def report():
    sm = json.load(open(os.path.join(KB, "wimcor_sample.json"), encoding="utf-8"))
    cd = json.load(open(os.path.join(KB, "wimcor_cands.json"), encoding="utf-8"))
    hit, tot, sizes = Counter(), Counter(), defaultdict(list)
    for o in sm:
        sp = cd.get(o["place_qid"], {})
        if o["coarse"] == "met":
            sort = SORT_OF[o["medium"]]
            tot[sort] += 1
            if o["referent_qid"] in sp.get(sort, []):
                hit[sort] += 1
        sizes[o["medium"]].append(sum(len(v) for v in sp.values()))
    for s in tot:
        print("%-10s gold referent in the space of its sort: %d/%d (%.0f%%)" % (s, hit[s], tot[s], 100 * hit[s] / tot[s]))
    for m, v in sizes.items():
        v.sort()
        print("%-10s space size (all sorts): median %d, 90th pct %d, max %d" % (m, v[len(v) // 2], v[int(len(v) * .9)], v[-1]))


if __name__ == "__main__":
    {"sample": sample, "cands": cands, "report": report, "named": cands_named, "search": cands_search, "report_search": report_search, "report_named": report_named}[sys.argv[1]]()
