#!/usr/bin/env python3
"""
Erdos Problem #261 pattern census (bulldoze campaign, Task 2-b).

CHARACTERIZATION (derived this session, hand-verified on n=1,4,5):
  n/2^n = sum_{a in S} a/2^a with S subseteq {n+1,...}, |S| = t >= 2
  <=> writing S = {n+j : j in Q}, Q subseteq {1..J} for some J >= max(Q), |Q| >= 2:
       sum_{j in Q} (n+j)/2^j = n
  <=> with P := {1..J} \ Q  (the complement!),
       A_P = sum_{j in P} 2^(J-j),   S_P = sum_{j in P} j*2^(J-j),
       n = (2^(J+1) - J - 2 - S_P) / (A_P + 1)

Enumerate ALL (J, A) patterns; A_P is the J-bit number with bit (J-j) set iff j in P.
Witness set of original problem: {n+j : j in {1..J}\\P}, requires J - |P| >= 2.
"""
import sys
from fractions import Fraction

JMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 22
NCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 500000

best = {}  # n -> (J, |P|, A)  prefer min J then min |P|

for J in range(1, JMAX + 1):
    base_const = (1 << (J + 1)) - J - 2
    contrib = [(J - b) << b for b in range(J)]
    S = 0
    popc = 0
    prevA = 0
    # A = 0: P = {}: n = 2^(J+1) - J - 2 (Borwein-Loring family), |Q| = J >= 2
    for A in range(0, 1 << J):
        if A:
            x = A ^ prevA
            while x:
                lb = x & (-x)
                b = lb.bit_length() - 1
                if A & lb:
                    S += contrib[b]; popc += 1
                else:
                    S -= contrib[b]; popc -= 1
                x -= lb
        prevA = A
        if base_const - S <= 0:
            continue
        if J - popc < 2:
            continue
        denom = A + 1
        numer = base_const - S
        if numer % denom == 0:
            n = numer // denom
            if 1 <= n <= NCAP:
                cur = best.get(n)
                if cur is None or (J, popc) < (cur[0], cur[1]):
                    best[n] = (J, popc, A)
    print(f"J={J}: cumulative certified {len(best)}", file=sys.stderr)

covered = sorted(best)
missing = [n for n in range(1, NCAP + 1) if n not in best]
print(f"JMAX={JMAX} NCAP={NCAP}")
print(f"certified: {len(covered)}  missing: {len(missing)}")
if missing:
    print("first 60 missing:", missing[:60])

# structure: J distribution
Jdist = {}
for n in covered:
    Jdist.setdefault(best[n][0], []).append(n)
for j in sorted(Jdist):
    ns = Jdist[j]
    print(f"  min-J={j}: count={len(ns)} range[{min(ns)},{max(ns)}]")

with open('certs.tsv', 'w') as f:
    for n in covered:
        J, popc, A = best[n]
        P = sorted(J - b for b in range(J) if (A >> b) & 1)
        Q = [j for j in range(1, J + 1) if j not in set(P)]
        f.write(f"{n}\t{J}\t{popc}\t{A}\t{len(Q)}\tP={P}\tQ={Q}\n")

def verify(n, J, A):
    P = set(J - b for b in range(J) if (A >> b) & 1)
    Q = [j for j in range(1, J + 1) if j not in P]
    if len(Q) < 2:
        return False
    lhs = sum(Fraction(n + j, 2 ** j) for j in Q)
    return lhs == n

ok = all(verify(n, *best[n]) for n in covered[:500])
print("sanity verify first 500:", "PASS" if ok else "FAIL")
print("max covered n:", max(covered) if covered else 0)
