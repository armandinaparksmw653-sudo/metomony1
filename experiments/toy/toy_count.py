# Toy finite model: Book = pairs (volume, work). Coercions: c1=vol (Book->Phy), c2=work (Book->Info).
from itertools import combinations

def three(items, key):
    """exists 3 items pairwise distinct AFTER coercion `key` (count in the image of the coercion)"""
    return len({key(b) for b in items}) >= 3

def three_book(items):           # distinctness in Book itself (pairs), as in Chatzikyriakidis-Luo's `Three Book`
    return len(set(items)) >= 3

def three_both(items):           # distinct in BOTH aspects, the criterion for "picked up and mastered three books"
    for tri in combinations(set(items), 3):
        if len({b[0] for b in tri}) == 3 and len({b[1] for b in tri}) == 3:
            return True
    return False

vol, work = (lambda b: b[0]), (lambda b: b[1])

scen = {
  # name: (books Fred picked up and mastered)
  "A: 2 copies of Elements + DC + Iliad + Odyssey":
      [("v1","Elements"),("v2","Elements"),("v3","DC"),("v4","Iliad"),("v5","Odyssey")],
  "B: trilogy in ONE volume + Elements + DC":
      [("v1","T1"),("v1","T2"),("v1","T3"),("v2","Elements"),("v3","DC")],
  "C: 3 volumes, 3 works (plain)":
      [("v1","a"),("v2","b"),("v3","c")],
  "D: 3 volumes but only 2 works":
      [("v1","a"),("v2","a"),("v3","b")],
}
print(f"{'scenario':50s} Book3 Phy3 Info3 Both3 | axiom(Book-distinct => Phy&Info-distinct) holds?")
for n, bs in scen.items():
    ax = all((x == y) or (vol(x) != vol(y) and work(x) != work(y)) for x in bs for y in bs)
    print(f"{n:50s} {three_book(bs)!s:5} {three(bs,vol)!s:5} {three(bs,work)!s:5} {three_both(bs)!s:5} | {ax}")
