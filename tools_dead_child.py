#!/usr/bin/env python3
# THE DEAD-CHILD AUTOMATON — full transition tables of the deformed Cantor tree.
# d(node, L) := which child (trit 0/1/2) dies at row L+1. Pure Cantor: d=2 always.
# For naturals the KILLER EVENT is d=0 (the zero-child dies) beyond support.
import sys

def digits3(n, j):
    return (n // (3 ** j)) % 3

def row(K, j):
    m = 3 ** (j + 1)
    return (pow(4, K, m) // (3 ** j)) % 3

print("=" * 70)
print("DEAD-CHILD TABLES: for each dust node at level L, which child dies at L+1")
print("=" * 70)

def dust_classes(L):
    dust = []
    for r in range(3 ** L):
        clean = all(row(r, j) != 2 for j in range(1, L + 1))
        if clean:
            dust.append(r)
    return dust

def dead_label(r, L):
    """node r (clean through row L); children r + t*3^L; which t dies at row L+1?"""
    dead = [t for t in range(3) if row(r + t * (3 ** L), L + 1) == 2]
    return dead

tables = {}
for L in range(1, 8):
    dust = dust_classes(L)
    tf = [r for r in dust if r % 3 == 1]
    tab = {}
    ndead_multi = 0
    for r in tf:
        dl = dead_label(r, L)
        if len(dl) != 1:
            ndead_multi += 1
        tab[r] = dl
    tables[L] = tab
    d0 = [r for r in tf if 0 in tab[r]]
    d1 = [r for r in tf if 1 in tab[r]]
    d2 = [r for r in tf if 2 in tab[r]]
    print(f"L={L} (children at row {L+1}): nodes with dead child 0: {len(d0)}, dead 1: {len(d1)}, dead 2: {len(d2)}, multi-dead: {ndead_multi}")
    if L >= 4:
        print(f"  dead-0 nodes: {d0}")
        print(f"  dead-1 nodes: {d1}")

print()
print("=" * 70)
print("THE CORRECTION-PERIOD LAW: d(node at level L) depends only on m mod 3^(L-1)?")
print("=" * 70)
# node r (K-class) at level L; m = (r-1)/3. Claim: row L+1 of 4^(r + t*3^L) as function of t
# is governed by m mod 3^(L-1): i.e., two nodes with same m mod 3^(L-1) have same dead label.
okc = badc = 0
for L in range(3, 8):
    tab = tables[L]
    bym = {}
    for r, dl in tab.items():
        m = (r - 1) // 3
        key = m % (3 ** (L - 1))
        if key in bym:
            if bym[key] != dl:
                badc += 1
            else:
                okc += 1
        else:
            bym[key] = dl
print(f"  same (m mod 3^(L-1)) => same dead label, L in [3,7]: {okc} consistent, {badc} VIOLATIONS")

print()
print("=" * 70)
print("THE d=0 KILLER EVENTS: nodes whose ZERO-child dies (naturals' death sentence)")
print("=" * 70)
for L in range(4, 8):
    tab = tables[L]
    d0 = [(r, (r - 1) // 3) for r in tab if 0 in tab[r]]
    print(f"L={L}: dead-0 nodes (r, m): {d0}")

print()
print("=" * 70)
print("PATH ANALYSIS: for naturals K (eventually-zero trits), walk the automaton")
print("=" * 70)
# survivors check via automaton walk for K < 20000 — must match direct scan
def automaton_survives(K, maxL=60):
    """walk: at each level L, K's trit_L must not be dead at node K mod 3^L."""
    for L in range(0, maxL):
        node = K % (3 ** L) if L > 0 else 0
        # need node clean; walk from root
        pass
    # simpler: direct row scan (same thing)
    for j in range(1, maxL + 1):
        if row(K, j) == 2:
            return False, j
    return True, None

# The real question: for K in [8, 20000], WHERE does the kill happen relative to K's support?
supp = lambda K: K.bit_length()  # not ternary; compute properly:
def support(K):
    s = 0
    while (3 ** (s + 1)) <= K:
        s += 1
    return s  # position of top trit

cat = {"within_support": 0, "just_above": 0, "deep": 0}
deep_cases = []
for K in range(8, 20000):
    ok, fr = automaton_survives(K, 60)
    if ok:
        print(f"  !! SURVIVOR K={K}")
        continue
    S = support(K)
    if fr <= S + 1:
        cat["within_support"] += 1
    elif fr <= 2 * S + 2:
        cat["just_above"] += 1
    else:
        cat["deep"] += 1
        deep_cases.append((K, fr, S))
print(f"  kill position vs support S (K in [8,20000)): {cat}")
print(f"  deep kills (fire_row > 2S+2): {len(deep_cases)}; sample: {deep_cases[:12]}")

print()
print("=" * 70)
print("THE CONSTANT-PATH LAW: for K with support S, rows S+2.. of 4^K (beyond K's trits)")
print("=" * 70)
# For dust survivors of the shallow phase: the node is frozen at K; the rows beyond S+1
# are the deep body. Check: row S+2.. of 4^K vs trits of (4^K - 4^r)/3^(S+1) structure
# where r = K mod 3^(S+1) = K (since K < 3^(S+1)): 4^K itself... instead check the
# c-alignment: rows S+2+j vs trit_j of (c_(S+1) * 4^(K - 3^(S+1)))? Use top-trit cut:
def c_mod(t, prec):
    M = 3 ** (t + 1 + prec)
    A = pow(4, 3 ** t, M)
    return ((A - 1) // (3 ** (t + 1))) % (3 ** prec)

print("  For DEEP-KILLED K: fire_row vs S and the trits of c_{S+1}*4^top stuff")
for (K, fr, S) in deep_cases[:10]:
    top = K // (3 ** S)  # top trit (1 or 2)
    r = K - top * (3 ** S)
    X = (c_mod(S, 24) * pow(4, r, 3 ** 24) ) % (3 ** 24) if top == 1 else None
    info = ""
    if X is not None:
        p = fr - S - 2
        if 0 <= p < 20:
            info = f"; trit_{p}(c_S*4^r)={(X // (3**p)) % 3}"
    print(f"    K={K}, S={S}, top={top}, fire_row={fr} (S+2+{fr-S-2}){info}")

print()
print("=" * 70)
print("VERIFY: dust tf classes at L=6 mod 729 == the green pin (32 residues)")
print("=" * 70)
d6 = [r for r in dust_classes(6) if r % 3 == 1]
print(f"  count: {len(d6)}")
print(f"  {sorted(d6)}")

print()
print("RECEIPT END — exact big-int, bounded.")
