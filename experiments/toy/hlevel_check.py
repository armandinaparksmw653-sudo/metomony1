# Finite model: do predictions differ between h-levels (-1: propositions, 0: sets of witnesses, 1: groupoids)?
from itertools import product
from collections import defaultdict

# ---- sense types (finite sets) and proof-relevant relations: (a,b) -> set of witnesses
Wrote  = {("D","CP"):{"a1"}, ("D","BK"):{"a2"}, ("T","WP"):{"a3"}}
Inst   = {("CP","c1"):{"i1"}, ("CP","c2"):{"i2"}, ("BK","c3"):{"i3"}, ("CP","c4"):{"i4"}, ("BK","c4"):{"i5"}}
Signed = {("D","c1"):{"s1"}, ("D","c4"):{"s2"}}                      # Author -> Copy directly
# second route through editions; c1 is a reprint belonging to TWO editions (two ways to be an instance)
HasEd  = {("CP","e1"):{"h1"}, ("CP","e1b"):{"h1b"}, ("CP","e2"):{"h2"}, ("BK","e3"):{"h3"}, ("BK","e4"):{"h4"}}
EdCopy = {("e1","c1"):{"k1"}, ("e1b","c1"):{"k1b"}, ("e1","c2"):{"k2"}, ("e2","c4"):{"k4"},
          ("e3","c3"):{"k3"}, ("e4","c4"):{"k5"}}

def compose(R, S):
    out = defaultdict(set)
    for (a,b),ws in R.items():
        for (b2,c),vs in S.items():
            if b == b2:
                for w,v in product(ws,vs): out[(a,c)].add((w,b,v))
    return dict(out)

def support(R):   return frozenset(R)                                   # level -1: only existence
def card(R):      return frozenset((k,len(v)) for k,v in R.items())     # level 0 : fibrewise cardinality (up to bijection)

R_work = compose(Wrote, Inst)
R_ed   = compose(compose(Wrote, HasEd), EdCopy)
routes = {"Wrote;Inst": R_work, "Wrote;HasEd;EdCopy": R_ed, "Signed": {k:v for k,v in Signed.items()}}

print("== K1/K2 existential readings (identical at all levels)")
read_works = {"CP"}; carried = {"c1","c3"}
print("read(Dostoevsky) :", any(a=="D" and b in read_works for (a,b) in Wrote))
print("carried(Dostoevsky) via works:", any(a=="D" and c in carried for (a,c) in R_work))

print("\n== K3 route equivalence: how many distinct READINGS does Coe(Author,Copy) have?")
def classes(keyf):
    cl = defaultdict(list)
    for n,R in routes.items(): cl[keyf(R)].append(n)
    return list(cl.values())
print("level -1 (compare supports)      :", classes(support), "-> #readings =", len(classes(support)))
print("level  0 (compare witness cards) :", classes(card),    "-> #readings =", len(classes(card)))

print("\n== K4 counting 'three Dostoevskys' (individuation)")
copies_D = {c for (a,c) in R_work if a=="D"}
works_D  = {b for (a,b) in Wrote if a=="D"}
n_deriv  = sum(len(v) for (a,c),v in R_work.items() if a=="D")
print("count in image (Copy):", len(copies_D), " count in image (Work):", len(works_D),
      " count of derivations (witnesses):", n_deriv)
print("  'three copies' true?", len(copies_D)>=3, "| 'three works' true?", len(works_D)>=3,
      "| naive derivation-count says 'three works'/'three copies' true?", n_deriv>=3, "(overcounts:", n_deriv, "vs", len(copies_D), ")")

print("\n== K5 'begin the book': Cand(h,b) = admissible event coercions")
def cand(h,b):
    s = {"read"}                      # anyone can read
    if (h,b) in Wrote: s.add("write") # authors can write
    return s
for h,b in [("Fred","CP"),("D","CP"),("T","WP")]:
    c = cand(h,b); print(f"Cand({h},{b}) = {sorted(c)}  |pi0| = {len(c)}  isProp? {len(c)<=1}")
print("  (deterministic case-function of Asher-Luo picks 'write' for authors; Cand exposes the residual ambiguity)")

print("\n== K7 groupoid of organisations across relocation (level 1)")
objs = [("Times",1980,"Fleet"),("Times",1990,"Wapping"),("Sun",1980,"Fleet"),("Sun",1990,"Wapping"),("Star",1990,"Fleet")]
iso  = [(x,y) for x in objs for y in objs if x[0]==y[0]]                      # morphism = same organisation
aut  = defaultdict(int)
for x,y in iso:
    if x==y: aut[x]+=1
print("automorphisms per object (all 1 => groupoid is equivalent to a SET of organisations):", set(aut.values()))
moved_groupoid = {(x,y) for x,y in iso if x[2]!=y[2]}                          # predicate on MORPHISMS
same = lambda x,y: x[0]==y[0]
moved_setoid   = {(x,y) for x in objs for y in objs if same(x,y) and x[2]!=y[2]}   # setoid encoding: pair + equivalence relation
print("moved(morphism) == moved(pair in setoid)?", moved_groupoid==moved_setoid)
invariant = lambda P: all(P(x)==P(y) for x,y in iso)
print("transport-invariant predicates on Org:  org-name:", invariant(lambda x:x[0]),
      "| at-Fleet-Street:", invariant(lambda x:x[2]=="Fleet"),
      " (the latter must be indexed by time, in either encoding)")
