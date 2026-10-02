"""Link ReLocaR location names to Wikidata and cache the result.

    python pipeline/wikidata.py link        # name -> candidate QIDs (wbsearchentities), cached
    python pipeline/wikidata.py describe    # instance-of / country / population of the chosen candidates, cached

Wikidata is CC0. Calls are cached in data/kb/ so that checking never needs the network.
"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import relocar  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
API = "https://www.wikidata.org/w/api.php"
UA = {"User-Agent": "metonymy-research/0.1 (research prototype; contact via GitHub repo)"}


def call(params, tries=4):
    url = API + "?" + urllib.parse.urlencode(dict(params, format="json"))
    for k in range(tries):
        try:
            return json.load(urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=30))
        except Exception:
            time.sleep(2 * (k + 1))
    return None


def names():
    rows = relocar.load("train") + relocar.load("test")
    return sorted({r["name"] for r in rows})


def link():
    os.makedirs(KB, exist_ok=True)
    path = os.path.join(KB, "links.json")
    cache = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else {}
    for i, n in enumerate(names()):
        if cache.get(n):
            continue
        r = call({"action": "wbsearchentities", "search": n, "language": "en", "limit": 5, "type": "item"})
        cache[n] = [{"qid": x["id"], "label": x.get("label"), "desc": x.get("description")} for x in (r or {}).get("search", [])]
        if i % 50 == 0:
            json.dump(cache, open(path, "w", encoding="utf-8"), ensure_ascii=False, indent=0)
            print(i, n, cache[n][:1], flush=True)
        time.sleep(0.15)
    json.dump(cache, open(path, "w", encoding="utf-8"), ensure_ascii=False, indent=0)
    print("linked", len(cache), "names;", sum(1 for v in cache.values() if not v), "without any candidate")


def describe():
    """Entities of all candidates: instance-of, coordinates, country, population, plus labels. Then pick the geographic one."""
    links = json.load(open(os.path.join(KB, "links.json"), encoding="utf-8"))
    path = os.path.join(KB, "entities.json")
    ents = json.load(open(path, encoding="utf-8")) if os.path.exists(path) else {}
    need = sorted({c["qid"] for v in links.values() for c in v} - set(ents))
    for i in range(0, len(need), 50):
        r = call({"action": "wbgetentities", "ids": "|".join(need[i:i + 50]), "props": "claims|labels|descriptions", "languages": "en"})
        for q, e in ((r or {}).get("entities") or {}).items():
            cl = e.get("claims", {})
            ids = lambda p: [c["mainsnak"]["datavalue"]["value"]["id"] for c in cl.get(p, []) if c["mainsnak"].get("datavalue")]
            ents[q] = {"label": e.get("labels", {}).get("en", {}).get("value"), "desc": e.get("descriptions", {}).get("en", {}).get("value"),
                       "P31": ids("P31"), "P17": ids("P17"), "P131": ids("P131"), "P36": ids("P36"), "P1376": ids("P1376"),
                       "coord": "P625" in cl, "pop": "P1082" in cl}
        print(i, len(need), flush=True)
        time.sleep(0.5)
    json.dump(ents, open(path, "w", encoding="utf-8"), ensure_ascii=False, indent=0)
    chosen = {}
    for n, cands in links.items():
        pick = next((c["qid"] for c in cands if ents.get(c["qid"], {}).get("coord")), None)
        chosen[n] = pick
    json.dump(chosen, open(os.path.join(KB, "chosen.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=0)
    print("chosen", sum(1 for v in chosen.values() if v), "of", len(chosen))





SPARQL = "https://query.wikidata.org/sparql"


def sparql(q, tries=2):
    url = SPARQL + "?format=json&query=" + urllib.parse.quote(q)
    for k in range(tries):
        try:
            return json.load(urllib.request.urlopen(urllib.request.Request(url, headers=UA), timeout=60))["results"]["bindings"]
        except Exception:
            time.sleep(3 * (k + 1))
    return None


def facts():
    """Institutions of the linked places: national teams and clubs (sport teams), executive and legislative bodies."""
    chosen = json.load(open(os.path.join(KB, "chosen.json"), encoding="utf-8"))
    qids = sorted({v for v in chosen.values() if v})
    out = {q: {"teams": [], "executive": [], "legislative": []} for q in qids}
    for i in range(0, len(qids), 30):
        vals = " ".join("wd:" + q for q in qids[i:i + 30])
        qs = {
            "teams": """SELECT ?p ?t ?tl ?sl WHERE { VALUES ?p { %s }
              { ?t wdt:P1532 ?p } UNION { ?t wdt:P159 ?p }
              ?t wdt:P641 ?s .
              SERVICE wikibase:label { bd:serviceParam wikibase:language "en". ?t rdfs:label ?tl. ?s rdfs:label ?sl } }""" % vals,
            "executive": """SELECT ?p ?t ?tl WHERE { VALUES ?p { %s } ?p wdt:P208 ?t .
              SERVICE wikibase:label { bd:serviceParam wikibase:language "en". ?t rdfs:label ?tl } }""" % vals,
            "legislative": """SELECT ?p ?t ?tl WHERE { VALUES ?p { %s } ?p wdt:P194 ?t .
              SERVICE wikibase:label { bd:serviceParam wikibase:language "en". ?t rdfs:label ?tl } }""" % vals,
        }
        for key, q in qs.items():
            for b in sparql(q) or []:
                p = b["p"]["value"].rsplit("/", 1)[1]
                lab = b["tl"]["value"]
                if key == "teams" and (" at the " in lab or lab.startswith("Q")):
                    continue
                out[p][key].append({"qid": b["t"]["value"].rsplit("/", 1)[1], "label": lab, "sport": b.get("sl", {}).get("value")})
        print("facts", i, len(qids), flush=True)
        time.sleep(1)
    json.dump(out, open(os.path.join(KB, "facts.json"), "w", encoding="utf-8"), ensure_ascii=False, indent=0)
    print({k: sum(1 for v in out.values() if v[k]) for k in ("teams", "executive", "legislative")}, "of", len(out))


if __name__ == "__main__":
    {"link": link, "describe": describe, "facts": facts}[sys.argv[1]]()
