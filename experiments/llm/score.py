"""Score ConMeC prompts with a causal LM, one forward pass per prompt.

For every (prompt family, sentence) it records the log-probabilities of the two answer tokens at the first
generated position ("Yes"/"No" or "A"/"B"), which gives a continuous score and avoids free-text parsing.
Results are appended to a JSONL file; a rerun skips what is already there, so an interrupted session
(Colab, Kaggle) can simply be restarted.

Example (Colab, T4):
  python experiments/llm/score.py --model Qwen/Qwen2.5-7B-Instruct --quant 4bit --out out_qwen.jsonl --limit 200
  python experiments/llm/score.py --model Qwen/Qwen2.5-7B-Instruct --quant 4bit --out out_qwen.jsonl
"""
import argparse
import json
import os
import random
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import data
import prompts


def load_model(name, quant, dtype_name):
    import torch
    from transformers import AutoModelForCausalLM, AutoTokenizer, BitsAndBytesConfig

    tok = AutoTokenizer.from_pretrained(name)
    tok.padding_side = "left"
    if tok.pad_token is None:
        tok.pad_token = tok.eos_token
    kwargs = {}
    if quant == "4bit":
        kwargs["quantization_config"] = BitsAndBytesConfig(
            load_in_4bit=True, bnb_4bit_quant_type="nf4", bnb_4bit_compute_dtype=torch.float16)
        kwargs["device_map"] = "auto"
    elif quant == "8bit":
        kwargs["quantization_config"] = BitsAndBytesConfig(load_in_8bit=True)
        kwargs["device_map"] = "auto"
    else:
        kwargs["torch_dtype"] = getattr(torch, dtype_name)
        if torch.cuda.is_available():
            kwargs["device_map"] = "auto"
    model = AutoModelForCausalLM.from_pretrained(name, **kwargs)
    model.eval()
    return tok, model


def render(tok, pid, row):
    msgs = prompts.messages(pid, row)
    if getattr(tok, "chat_template", None):
        return tok.apply_chat_template(msgs, tokenize=False, add_generation_prompt=True)
    # models without a chat template (used only for testing the script)
    return msgs[0]["content"] + "\n\n" + msgs[1]["content"] + "\nAnswer:"


def answer_ids(tok):
    ids = {}
    for pid, (a, b) in prompts.ANSWER_TOKENS.items():
        for t in (a, b):
            enc = tok.encode(t, add_special_tokens=False)
            if len(enc) != 1:
                print("warning: answer %r is %d tokens; using the first" % (t, len(enc)), file=sys.stderr)
            ids[t] = enc[0]
    return ids


def done_keys(path):
    keys = set()
    if os.path.exists(path):
        with open(path, encoding="utf-8") as f:
            for line in f:
                try:
                    r = json.loads(line)
                    keys.add((r["id"], r["prompt"]))
                except Exception:
                    pass
    return keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default="Qwen/Qwen2.5-7B-Instruct")
    ap.add_argument("--quant", default="4bit", choices=["4bit", "8bit", "none"])
    ap.add_argument("--dtype", default="float16")
    ap.add_argument("--out", default="out.jsonl")
    ap.add_argument("--prompts", default=",".join(prompts.PROMPT_IDS))
    ap.add_argument("--batch", type=int, default=16)
    ap.add_argument("--limit", type=int, default=0, help="score only a fixed random subset of this many sentences")
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--csv", default=data.DEFAULT_PATH)
    args = ap.parse_args()

    import torch

    rows = data.load(args.csv)
    if args.limit:
        rows = random.Random(args.seed).sample(rows, args.limit)
    pids = args.prompts.split(",")
    tok, model = load_model(args.model, args.quant, args.dtype)
    ids = answer_ids(tok)
    done = done_keys(args.out)

    tasks = [(pid, r) for pid in pids for r in rows if (r["id"], pid) not in done]
    texts = {(pid, r["id"]): render(tok, pid, r) for pid, r in tasks}
    tasks.sort(key=lambda t: len(texts[(t[0], t[1]["id"])]))
    print("%d prompts to score (%d already done)" % (len(tasks), len(done)), flush=True)

    device = next(model.parameters()).device
    t0 = time.time()
    n = 0
    bs = args.batch
    i = 0
    with open(args.out, "a", encoding="utf-8") as out:
        while i < len(tasks):
            batch = tasks[i:i + bs]
            enc = tok([texts[(p, r["id"])] for p, r in batch], return_tensors="pt", padding=True)
            enc = {k: v.to(device) for k, v in enc.items()}
            try:
                with torch.no_grad():
                    logits = model(**enc).logits[:, -1, :].float()
            except torch.cuda.OutOfMemoryError:
                torch.cuda.empty_cache()
                bs = max(1, bs // 2)
                print("out of memory, batch size now %d" % bs, flush=True)
                continue
            logp = torch.log_softmax(logits, dim=-1)
            for (pid, r), row_lp in zip(batch, logp):
                a, b = prompts.ANSWER_TOKENS[pid]
                la, lb = row_lp[ids[a]].item(), row_lp[ids[b]].item()
                out.write(json.dumps({"id": r["id"], "prompt": pid, "lp": {a: la, b: lb}}) + "\n")
            out.flush()
            i += len(batch)
            n += len(batch)
            if (n // len(batch)) % 20 == 0:
                rate = n / (time.time() - t0)
                print("%d/%d  %.1f prompts/s" % (i, len(tasks), rate), flush=True)
    print("finished in %.1f min" % ((time.time() - t0) / 60))


if __name__ == "__main__":
    main()
