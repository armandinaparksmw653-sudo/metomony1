"""Input for the language-model annotation of frames: L2 frames with at least 5 occurrences and all L1 frames, with example snippets.

    python pipeline/frames_input.py   # writes results/frames_input.jsonl (not tracked: corpus text)
"""
import json
import zlib
import os
import random
import sys
from collections import defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import frames  # noqa: E402
import wimcor  # noqa: E402

KB = os.path.join(HERE, "..", "data", "kb")
table = json.load(open(os.path.join(KB, "wimcor_frames.json"), encoding="utf-8"))
out = []
for f, e in table.items():
    if e["n"] >= 5:
        rng = random.Random(zlib.crc32(f.encode()) % 100000)
        ex = rng.sample(e["ex"], min(4, len(e["ex"])))
        out.append({"frame": f, "level": 2, "n": e["n"], "ex": ex})
l1 = defaultdict(list)
cnt = defaultdict(int)
rng = random.Random(5)
for r in wimcor.load():
    _, f1 = frames.frame_of(r)
    cnt[f1] += 1
    if len(l1[f1]) < 30:
        l1[f1].append(frames.snippet(r))
    elif rng.random() < 0.01:
        l1[f1][rng.randrange(30)] = frames.snippet(r)
for f, ex in l1.items():
    out.append({"frame": f, "level": 1, "n": cnt[f], "ex": random.Random(7).sample(ex, min(4, len(ex)))})
with open(os.path.join(HERE, "..", "results", "frames_input.jsonl"), "w", encoding="utf-8") as fo:
    for o in out:
        fo.write(json.dumps(o, ensure_ascii=False) + "\n")
print(len(out), "frames to annotate (L2 with n>=5:", sum(1 for o in out if o["level"] == 2), ", L1:", sum(1 for o in out if o["level"] == 1), ")")
