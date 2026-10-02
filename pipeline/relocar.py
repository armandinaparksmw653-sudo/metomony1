"""ReLocaR loader (Gritta et al. 2017; sentences from Wikipedia, one annotated location per sentence).

The raw XML is downloaded to data/raw/relocar (not stored in the repository, the data is GPL-3 licensed upstream):
https://github.com/milangritta/Minimalist-Location-Metonymy-Resolution (ReLocaR_XML/ReLocaR_{Train,Test}.xml)
"""
import html
import os
import re

RAW = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "data", "raw", "relocar")
LABEL = {"lit": "literal", "met": "metonymic", "mixed": "mixed", "mix": "mixed"}


def load(split):
    text = open(os.path.join(RAW, "ReLocaR_%s.xml" % split.capitalize()), encoding="utf-8").read()
    rows = []
    for m in re.finditer(r'<sample number="(\d+)">(.*?)</sample>', text, re.S):
        body = m.group(2).strip()
        loc = re.search(r'<loc reading="(\w+)">(.*?)</loc>', body, re.S)
        if not loc:
            continue
        sent = html.unescape(re.sub(r"</?loc[^>]*>", "", body))
        start = body.index(loc.group(0))
        rows.append({"id": "%s-%s" % (split, m.group(1)), "split": split, "label": LABEL[loc.group(1)],
                     "name": html.unescape(loc.group(2)), "sentence": sent, "start": start})
    return rows


if __name__ == "__main__":
    for s in ("train", "test"):
        r = load(s)
        c = {}
        for x in r:
            c[x["label"]] = c.get(x["label"], 0) + 1
        print(s, len(r), c, "unique names:", len({x["name"] for x in r}))
