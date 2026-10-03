"""WiMCor loader (Mathews and Strube 2020; CC BY-SA 3.0; https://github.com/nlpAThits/WiMCor).

The data is downloaded to data/raw/wimcor (not stored in the repository):
https://kevinalexmathews.github.io/files/wimcor-v1.1.tar.gz  ->  data/raw/wimcor/full/wimcor-v1.1/

A sample is a Wikipedia passage with one annotated place name: <pmw coarse='lit|met' medium='LOCATION|INSTITUTE|TEAM|EVENT|ARTIFACT'
fine='Wikipedia title'>surface</pmw>. For literal samples the fine label is the place page, for metonymic ones the referent page.
The metonymic pairs (place page, referent page) the corpus was harvested from are in metonymic-pairs/.
"""
import html
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "..", "data", "raw", "wimcor", "full", "wimcor-v1.1")
TAG = re.compile(r"<pmw coarse='(\w+)' medium='(\w+)' fine='(.*?)'>(.*?)</pmw>", re.S)
PAIR = re.compile(r"^Hit (.*): \(<(.*)>, <(.*)>\)$")
PAIR_FILES = {"ARTIFACT": "LOCATION-for-ARTIFACT", "EVENT": "LOCATION-for-EVENT", "INSTITUTE": "LOCATION-for-INSTITUTION", "TEAM": "LOCATION-for-TEAM"}


def load(split="full-corpus"):
    """Samples of a partition: id, coarse, medium, referent (fine label), surface, left/right context."""
    name = split if split.endswith("corpus") else split + "-partition"
    text = open(os.path.join(ROOT, "dataset", "xml", name + ".xml"), encoding="utf-8").read()
    rows = []
    for i, m in enumerate(re.finditer(r"<sample>(.*?)</sample>", text, re.S)):
        s = m.group(1)
        t = TAG.search(s)
        if not t:
            continue
        coarse, medium, fine, surface = t.groups()
        left, right = s[:t.start()], s[t.end():]
        rows.append({"id": "%s-%d" % (split, i), "coarse": coarse, "medium": medium, "fine": html.unescape(fine),
                     "surface": html.unescape(surface), "left": html.unescape(left), "right": html.unescape(right)})
    return rows


def sentence(r):
    return (r["left"] + r["surface"] + r["right"]).strip()


def pairs():
    """Metonymic pairs (place page, referent page, medium, disambiguation page the pair was found under)."""
    out = []
    for medium, fn in PAIR_FILES.items():
        for line in open(os.path.join(ROOT, "metonymic-pairs", fn), encoding="utf-8"):
            m = PAIR.match(line.strip())
            if m:
                out.append({"hit": html.unescape(m.group(1)), "place": html.unescape(m.group(2)), "referent": html.unescape(m.group(3)), "medium": medium})
    return out


if __name__ == "__main__":
    ps = pairs()
    print(len(ps), "pairs;", len({p["place"] for p in ps}), "places;", len({p["referent"] for p in ps}), "referents")
    rs = load("test")
    print(len(rs), "test samples; example:", rs[0]["surface"], "->", rs[0]["fine"], rs[0]["medium"])
