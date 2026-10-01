"""Prompt templates for ConMeC.

Three families, all answered by the first token so that one forward pass gives a score:
  P0  : plain yes/no question about metonymic use (no category information);
  P1  : yes/no question conditioned on the metonymy type given by the dataset (as in the ConMeC paper, whose
        prompts are category dependent);
  S1a/S1b : forced choice between the literal sense and the metonymic sense of the type, with both orders of
        the options (to cancel position bias).
The types follow Pedinotti and Lenci (2020) as used by ConMeC.
"""

SYSTEM = "You are a careful linguist. Answer with a single word or letter."

DEFINITION = (
    "Metonymy is a figure of speech in which a word is used to refer to something associated with its "
    "literal referent (for example, \"the kettle is boiling\" refers to the water in the kettle)."
)

# literal sense, metonymic sense, and a yes/no question for each type
TYPES = {
    "CONTAINER": {
        "name": "container-for-content",
        "literal": "the container itself",
        "meto": "the contents of the container, or an activity involving the contents",
        "q": "Does the target word refer to the contents of the container (or an activity involving them) "
             "rather than to the container itself?",
    },
    "PRODUCER": {
        "name": "producer-for-product",
        "literal": "the producer itself (a person or an organization)",
        "meto": "what the producer produced (their work, music, writing or other output)",
        "q": "Does the target word refer to what the producer produced (their work or output) "
             "rather than to the producer itself?",
    },
    "PRODUCT": {
        "name": "product-for-producer",
        "literal": "the product itself (a publication, programme or other product)",
        "meto": "the people or organization that produce the product (its editors, authors, publisher)",
        "q": "Does the target word refer to the people or organization that produce the product "
             "rather than to the product itself?",
    },
    "LOCATION": {
        "name": "location-for-located",
        "literal": "the physical place",
        "meto": "the people, institutions, activities or events located at the place",
        "q": "Does the target word refer to the people, institutions or activities located at the place "
             "rather than to the physical place itself?",
    },
    "CAUSER": {
        "name": "causer-for-result",
        "literal": "the causer itself (an instrument, agent or thing)",
        "meto": "the result or effect the causer brings about (for example the sound or music it produces)",
        "q": "Does the target word refer to the result or effect brought about by the causer "
             "rather than to the causer itself?",
    },
    "POSSESSED": {
        "name": "possessed-for-possessor",
        "literal": "the possessed object itself",
        "meto": "the person who possesses or uses the object",
        "q": "Does the target word refer to the person who possesses or uses the object "
             "rather than to the object itself?",
    },
}

PROMPT_IDS = ["P0", "P1", "S1a", "S1b"]
ANSWER_TOKENS = {"P0": ("Yes", "No"), "P1": ("Yes", "No"), "S1a": ("A", "B"), "S1b": ("A", "B")}
# For every prompt the FIRST listed token means "metonymic" except S1b, where the options are swapped.


def user_message(pid, row):
    t = TYPES[row["category"]]
    base = "Sentence: %s\nTarget word: %s\n\n" % (row["sentence"], row["target"])
    if pid == "P0":
        return (DEFINITION + "\n\n" + base +
                "Is the target word used metonymically in this sentence (that is, does it refer to something "
                "associated with its literal referent rather than the literal referent itself)? "
                "Answer Yes or No.")
    if pid == "P1":
        return (DEFINITION + " Here the type is %s.\n\n" % t["name"] + base + t["q"] + " Answer Yes or No.")
    if pid in ("S1a", "S1b"):
        a, b = (t["meto"], t["literal"]) if pid == "S1a" else (t["literal"], t["meto"])
        return (DEFINITION + "\n\n" + base +
                "Which reading of the target word fits this sentence better?\n"
                "(A) %s\n(B) %s\nAnswer A or B." % (a, b))
    raise ValueError(pid)


def metonymic_token(pid):
    """The answer token that means 'metonymic'."""
    yes_no = ANSWER_TOKENS[pid]
    return {"P0": yes_no[0], "P1": yes_no[0], "S1a": "A", "S1b": "B"}[pid]


def messages(pid, row):
    return [{"role": "system", "content": SYSTEM}, {"role": "user", "content": user_message(pid, row)}]
