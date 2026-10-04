"""Predicate frames for WiMCor: the local construction in which the place name occurs.

    python pipeline/frames.py        # frame index of the whole corpus, frame table with counts and examples

A frame is the two tokens before the mention inside its sentence (a sentence boundary becomes the token <s>), for example
"graduated from", "played for", "battle of", "<s> in". It is the cheap stand-in for the predicate of a typed abstract-syntax term:
"graduated from ___" requires an Institute, "born in ___" a Place. The lexicon frame -> required sort is built once per frame
(by statistics of the training partition and by a language model, see notebooks), then every sentence is typed by lookup.
Backoff: two tokens, then one token, then nothing.

Outputs (not tracked, they contain corpus text): data/kb/wimcor_frame_index.json (sentence id -> [L2 frame, L1 frame, partition]),
data/kb/wimcor_frames.json (frame -> counts per medium in train, total, examples).
"""
import json
import os
import random
import re
import sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import wimcor  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
TOK = re.compile(r"\w+(?:'\w+)?|[^\w\s]")
END = {".", "!", "?", ";"}


def left_tokens(left, k=2):
    toks = TOK.findall(left.lower())
    out = []
    for t in reversed(toks):
        if t in END:
            out.append("<s>")
            break
        out.append(t)
        if len(out) == k:
            break
    out.reverse()
    if not out:
        out = ["<s>"]
    return out


def frame_of(r):
    t = left_tokens(r["left"], 2)
    return " ".join(t[-2:]), " ".join(t[-1:])


def snippet(r, width=60):
    """Left context inside the sentence with the mention replaced by [X], and a few tokens after it."""
    left = r["left"]
    cut = max(left.rfind(". "), left.rfind("! "), left.rfind("? "))
    left = left[cut + 2:] if cut >= 0 else left
    left = " ".join(left.split()[-10:])
    right = " ".join(r["right"].split()[:6])
    return (left + " [X] " + right).strip()


def main():
    index, table = {}, defaultdict(lambda: {"train": Counter(), "n": 0, "ex": []})
    rng = random.Random(3)
    for part, name in (("train", "train"), ("val", "val"), ("test", "test")):
        for r in wimcor.load(name):
            f2, f1 = frame_of(r)
            index[r["id"]] = [f2, f1, part, r["medium"], r["coarse"]]
            e = table[f2]
            e["n"] += 1
            if part == "train":
                e["train"][r["medium"]] += 1
            if len(e["ex"]) < 40:
                e["ex"].append(snippet(r))
            elif rng.random() < 0.02:
                e["ex"][rng.randrange(40)] = snippet(r)
    out = {f: {"n": e["n"], "train": dict(e["train"]), "ex": e["ex"]} for f, e in table.items()}
    json.dump(index, open(os.path.join(KB, "wimcor_frame_index.json"), "w", encoding="utf-8"), ensure_ascii=False)
    json.dump(out, open(os.path.join(KB, "wimcor_frames.json"), "w", encoding="utf-8"), ensure_ascii=False)
    tot = sum(e["n"] for e in table.values())
    cnt = sorted((e["n"] for e in table.values()), reverse=True)
    print(len(index), "sentences;", len(table), "distinct frames")
    for k in (100, 500, 1000, 3000, 5000, 10000):
        print("top %5d frames cover %.1f%% of all sentences" % (k, 100 * sum(cnt[:k]) / tot))
    print("frames with at least 5 occurrences:", sum(1 for c in cnt if c >= 5), "covering %.1f%%" % (100 * sum(c for c in cnt if c >= 5) / tot))


if __name__ == "__main__":
    main()
