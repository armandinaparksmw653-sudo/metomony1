# Two routes Author -> Copy with equal witness sets; 2-cells = bijections of witness sets that preserve all
# language-accessible structure (predicates). Count valid 2-cells = "number of ways the routes are equivalent".
from itertools import permutations

def valid_2cells(W1, W2, predicates):
    """bijections f: W1->W2 s.t. every predicate (a function on witnesses) is preserved: p1(w)==p2(f(w))"""
    out = []
    for perm in permutations(W2):
        f = dict(zip(W1, perm))
        if all(p1(w) == p2(f[w]) for (p1, p2) in predicates for w in W1):
            out.append(f)
    return out

# Situation A: two physically INDISTINGUISHABLE copies c1,c2 of one edition, reached by two routes
W_work = [("CP","c1"), ("CP","c2")]            # route via Work -> Inst
W_ed   = [("e1","c1"), ("e1","c2")]            # route via Edition -> Copy
pA = [(lambda w: "edition-e1/CP", lambda w: "edition-e1/CP")]      # only observable property: same edition, same work
print("A: indistinguishable copies           -> valid 2-cells:", len(valid_2cells(W_work, W_ed, pA)))

# Situation B: add ONE observable difference between the copies (e.g. 'Fred's copy' vs 'the library's copy')
owner = {"c1":"Fred", "c2":"Lib"}
pB = [(lambda w: owner[w[1]], lambda w: owner[w[1]])]
print("B: copies differ by an observable property -> valid 2-cells:", len(valid_2cells(W_work, W_ed, pB)))

# Situation C: Marx/Engels-style symmetric co-authorship, round trip Author -> Work -> Author
coauth = [("Marx","Manifesto"),("Engels","Manifesto")]
W_loop = [("Marx","Manifesto","Marx"),("Marx","Manifesto","Engels")]   # witnesses of a round trip starting at Marx
print("C: round-trip witnesses from Marx:", [w[2] for w in W_loop], "(holonomy = which co-author we land on)")
