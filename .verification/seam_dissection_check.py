#!/usr/bin/env python3
"""SEAM DISSECTION — new receipts attacking the SeedOneWitness seam.

The seam: forall s,n >= 1: SeedOneWitness (prefixOffset s + 4^(3^s)*canonicalTail (s+1) n)
  <=> Navigation (canonicalTail s (1+3n))   [prefix_one_tail_shape + navigation_prefixed_one_iff_seed_one, both green]

Dissections:
  D-A  seam sweep: Navigation on canonicalTail s (1+3n) — witness-depth law
  D-B  unit-tail base family: Navigation (lteCoeff s) — the c_infty row-4 pin
  D-D  stabilization law: lteCoeff (s+1) = lteCoeff s mod 3^(s+1)  (cube-lift, Lean-provable)
  D-E  the s=1 open family (n = 3^k * m, m = 1 mod 3) — witness law vs k
  D-C  parent decomposition transport: X = z_s + 4^(3^s)*T — where the parent witness lives
  D-F  fire-vs-happy gap on canonical tails (carry-quarter law)
  D-2  violator separator: random-T forced-prefix WCP violators vs canonical T residues

Run: python3 seam_dissection_check.py   (pure Python, a few minutes)
"""
import random

# ---------------- core modular machinery ----------------

def digit3(X, p):
    return (X // 3 ** p) % 3

def carry4(X, p):
    return 4 * (X % 3 ** p) // 3 ** p

def happy(C, d):
    return d == 2 and C in (0, 3)

def tail_mod(s, b, J):
    """canonicalTail s b = 4^(3^s * b) / 3^(s+1), reduced mod 3^J (rows 0..J-1)."""
    m = 3 ** (s + 1 + J)
    v = pow(4, (3 ** s) * b, m)
    return ((v - 1) // 3 ** (s + 1)) % (3 ** J)

def nav_happy_rows(Xmod, J):
    """all p with HappyCell (carry4 X p) (digit3 X p), from X mod 3^J."""
    out = []
    for p in range(J):
        d = (Xmod // 3 ** p) % 3
        c = 4 * (Xmod % 3 ** p) // 3 ** p
        if happy(c, d):
            out.append((p, d, c))
    return out

def fire_rows(Xmod, J):
    return [p for p in range(J) if (Xmod // 3 ** p) % 3 == 2]

def v3(x):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % 3 == 0:
        v += 1
        x //= 3
    return v

def trits(Xmod, n):
    return [digit3(Xmod, p) for p in range(n)]

# ---------------- D-A: seam sweep ----------------

def d_a():
    print("=" * 72)
    print("D-A  SEAM SWEEP: Navigation (canonicalTail s (1+3n)), s in 1..5, n in 1..160")
    J = 220
    fails = []
    law = {}
    for s in range(1, 6):
        pmins, qmins = [], []
        for n in range(1, 161):
            P = tail_mod(s, 1 + 3 * n, J)          # parent tail (the seam object)
            Q = tail_mod(s + 1, n, J)              # child tail
            hp = nav_happy_rows(P, J)
            hq = nav_happy_rows(Q, J)
            if not hp:
                fails.append((s, n, "parent-no-witness"))
                continue
            pmin = hp[0][0]
            qmin = hq[0][0] if hq else None
            pmins.append(pmin)
            qmins.append(qmin)
            law[(s, n)] = (pmin, qmin)
        if pmins:
            print(f"  s={s}: parent witness rows: min={min(pmins)} max={max(pmins)} "
                  f"mean={sum(pmins)/len(pmins):.1f}; "
                  f"child rows: min={min(q for q in qmins if q is not None)} "
                  f"max={max(q for q in qmins if q is not None)}")
    print(f"  seam failures (no parent witness in {J} rows): {len(fails)}")
    for f in fails[:10]:
        print(f"    FAIL {f}")
    # witness-row law vs n-class
    print("  witness row p* by (n mod 3) and v3(n):")
    for s in range(1, 6):
        for r in (0, 1, 2):
            vals = [law[(s, n)][0] for n in range(1, 161) if n % 3 == r and (s, n) in law]
            if vals:
                print(f"    s={s} n%3={r}: p* min={min(vals)} max={max(vals)} mean={sum(vals)/len(vals):.1f}")
    # large-prefix check: n = 3^k * m, k large -> witness near origin row?
    print("  parent witness row p* vs k = v3(n) (n = 3^k m, m 3-free):")
    for s in range(1, 6):
        row = []
        for k in range(0, 6):
            vals = [law[(s, n)][0] for n in range(1, 161)
                    if v3(n) == k and (s, n) in law]
            if vals:
                row.append(f"k={k}:{min(vals)}-{max(vals)}")
        print(f"    s={s}: " + "  ".join(row))
    return law

# ---------------- D-B + D-D: unit tails ----------------

def d_b():
    print("=" * 72)
    print("D-B  UNIT-TAIL BASE FAMILY: Navigation (lteCoeff s) for s in 1..22")
    J = 48
    for s in range(1, 23):
        X = tail_mod(s, 1, J)
        hs = nav_happy_rows(X, J)
        if hs:
            p, d, c = hs[0]
            print(f"  s={s:2d}: FIRST happy row = {p:2d} (digit={d}, carry={c}); "
                  f"happy rows: {[h[0] for h in hs[:8]]}; lteCoeff s mod 243 = {X % 243}")
        else:
            print(f"  s={s:2d}: NO happy row in {J} rows (!!)  mod 243 = {X % 243}")
    c_infty = tail_mod(22, 1, 30)
    print(f"  c_infty trits (lteCoeff 22, rows 0..17): {trits(c_infty, 18)}")
    print(f"  c_infty 2-positions below 18: {[p for p in range(18) if digit3(c_infty, p) == 2]}")
    print("  D-D  stabilization: lteCoeff (s+1) == lteCoeff s (mod 3^(s+1))?")
    ok = True
    for s in range(1, 21):
        a = tail_mod(s, 1, s + 2)
        b = tail_mod(s + 1, 1, s + 2)
        if a % 3 ** (s + 1) != b % 3 ** (s + 1):
            ok = False
            print(f"    s={s}: STABILIZATION BREAKS")
    print(f"    all s in 1..20: {'HOLDS' if ok else 'FAILS'}")

# ---------------- D-E: the s=1 open family ----------------

def d_e():
    print("=" * 72)
    print("D-E  S=1 OPEN FAMILY: n = 3^k * m, m = 1 mod 3 (3-free), parent (s=1, 1+3n)")
    J = 240
    print("  (k, m) -> parent happy row p*, child happy row q*, parent fire row:")
    for k in range(0, 7):
        line = []
        for m in [1, 4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, 37, 40]:
            if m % 3 != 1 or m % 3 == 0:
                continue
            n = (3 ** k) * m
            P = tail_mod(1, 1 + 3 * n, J)
            Q = tail_mod(2, n, J)
            hp = nav_happy_rows(P, J)
            hq = nav_happy_rows(Q, J)
            pmin = hp[0][0] if hp else None
            qmin = hq[0][0] if hq else None
            line.append((m, pmin, qmin))
        ps = [x[1] for x in line if x[1] is not None]
        print(f"  k={k}: p* values {ps}")
        if k in (0, 1, 2):
            print(f"        detail: {line[:6]}")

# ---------------- D-C: parent decomposition ----------------

def d_c():
    print("=" * 72)
    print("D-C  PARENT DECOMPOSITION: X = z_s + 4^(3^s)*T; rows < s+1 = digits of z_s + T")
    J = 80
    below = above = 0
    sanity_ok = True
    correl = []
    for s in range(1, 5):
        z = tail_mod(s, 1, J + 1) // 3          # prefixOffset s mod 3^J
        A = pow(4, 3 ** s, 3 ** J)              # 4^(3^s) mod 3^J
        for n in range(1, 61):
            T = tail_mod(s + 1, n, J)           # child tail mod 3^J
            X = (z + A * T) % (3 ** J)
            P = tail_mod(s, 1 + 3 * n, J)
            if X != P:
                sanity_ok = False
                print(f"  SANITY FAIL at s={s} n={n}")
            # check rows below s+1 equal digits of z + T
            lowOK = all(digit3(X, p) == digit3((z + T) % (3 ** J), p) for p in range(s + 1))
            if not lowOK:
                sanity_ok = False
                print(f"  LOW-ROWS FAIL s={s} n={n}")
            hp = nav_happy_rows(P, J)
            hq = nav_happy_rows(T, J)
            if hp and hq:
                pmin, qmin = hp[0][0], hq[0][0]
                correl.append((s, n, qmin, pmin))
                if pmin < s + 1:
                    below += 1
                else:
                    above += 1
    print(f"  sanity (X = z_s + A*T == parent tail; rows<s+1 == digits of z+T): "
          f"{'HOLDS' if sanity_ok else 'FAILS'}")
    print(f"  parent minimal witness row: below s+1 (perturbation zone): {below}, "
          f"at/above s+1 (product zone): {above}")
    dq = {}
    for s, n, q, p in correl:
        dq.setdefault(q - p, 0)
        dq[q - p] += 1
    print(f"  child-row minus parent-row (q*-p*) histogram: {dict(sorted(dq.items()))}")

# ---------------- D-F: fire vs happy gap ----------------

def d_f():
    print("=" * 72)
    print("D-F  FIRE-VS-HAPPY GAP on canonical tails (s, 1+3n): carry at the fire rows")
    J = 120
    at_fire_happy = 0
    tot_fire = 0
    quarter = {0: 0, 1: 0, 2: 0}
    for s in range(1, 5):
        for n in range(1, 121):
            X = tail_mod(s, 1 + 3 * n, J)
            for p in fire_rows(X, J)[:3]:
                c = carry4(X, p)
                tot_fire += 1
                if c in (0, 3):
                    at_fire_happy += 1
                r = (X % 3 ** p) / (3 ** p) if p > 0 and 3 ** p < 10 ** 12 else None
                if r is not None:
                    if r < 0.25:
                        quarter[0] += 1
                    elif r > 0.75:
                        quarter[2] += 1
                    else:
                        quarter[1] += 1
    print(f"  fire rows (first 3 per tail): {tot_fire}; carry in (0,3) at fire: "
          f"{at_fire_happy} ({100*at_fire_happy/max(tot_fire,1):.1f}%)")
    print(f"  tail mod 3^p quarter at fire rows: bottom={quarter[0]} middle={quarter[1]} top={quarter[2]}")

# ---------------- D-2: violator separator ----------------

def outDigit(C, d):
    return (C + 4 * d) % 3

def nextCarry(C, d):
    return (C + 4 * d) // 3

dP = {0: 19, 1: 56, 2: 21}
cP = {0: 0, 1: -19, 2: -56, 3: 0}

def surviveI(C, d):
    def twoI(x):
        return 1 if x == 2 else 0
    def mo(a, dd):
        return (a + 2 * dd) % 3
    mid = mo(C // 2, d)
    fin = mo(C % 2, mid)
    return twoI(d) * twoI(mid) + twoI(mid) * twoI(fin)

def CD(C, d):
    return (dP[outDigit(C, d)] - 4 * dP[d] + cP[C] - 3 * cP[nextCarry(C, d)]
            + 84 * surviveI(C, d))

def reverseCrossCode(colC, colD, N):
    s = 0
    for t in range(N):
        s = 4 * s + CD(colC[t], colD[t])
    return s

def WCP(C, d, N, K):
    return sum((3 ** p) * reverseCrossCode(
        [C[t][p] for t in range(N)], [d[t][p] for t in range(N)], N)
        for p in range(K))

def rectangle(E, N, b, K):
    W = b + K + 1
    X = [E * (4 ** t) for t in range(N + 1)]
    C = [[carry4(X[t], p) for p in range(W)] for t in range(N + 1)]
    D = [[digit3(X[t], p) for p in range(W)] for t in range(N + 1)]
    return C, D

def d_2():
    print("=" * 72)
    print("D-2  VIOLATOR SEPARATOR: forced-prefix random-T violators vs canonical T")
    random.seed(11)
    viol_T = []
    ok_T = []
    for _ in range(30000):
        s = random.randint(1, 3)
        N = 3 ** s
        b = s + 2
        K = random.randint(2, 7)
        T = random.randint(0, 3 ** (K + 2) - 1)
        E = 1 + (3 ** b) * T
        C, D = rectangle(E, N, b, K)
        if all(not happy(C[N][b + j], D[N][b + j]) for j in range(K)):
            w = WCP([[C[t][b + i] for i in range(K)] for t in range(N + 1)],
                    [[D[t][b + i] for i in range(K)] for t in range(N + 1)],
                    N, K)
            (viol_T if w > 0 else ok_T).append((s, T))
    canon_T = []
    for s in range(1, 4):
        for n in range(1, 61):
            canon_T.append((s, tail_mod(s + 1, n, 12)))  # canonical child tails mod 3^12
    def feats(T):
        return (T % 3, T % 9, T % 27, v3(T - 1) if T > 0 else -1,
                v3(T + 1) if T >= 0 else -1)
    print(f"  violators (parent-bad & WCP>0): {len(viol_T)}; "
          f"non-violators (parent-bad & WCP<=0): {len(ok_T)}")
    fv = {}
    for s, T in viol_T:
        k = (s, T % 9)
        fv[k] = fv.get(k, 0) + 1
    print(f"  violator T mod 9 distribution by s: {dict(sorted(fv.items()))}")
    fc = {}
    for s, T in canon_T:
        k = (s, T % 9)
        fc[k] = fc.get(k, 0) + 1
    print(f"  canonical T mod 9 distribution by s: {dict(sorted(fc.items()))}")
    v9 = {}
    for s, T in viol_T:
        v9[T % 9] = v9.get(T % 9, 0) + 1
    c9 = {}
    for s, T in canon_T:
        c9[T % 9] = c9.get(T % 9, 0) + 1
    print(f"  violator T%9 total: {dict(sorted(v9.items()))}")
    print(f"  canonical T%9 total: {dict(sorted(c9.items()))}")
    v27 = {}
    for s, T in viol_T:
        v27[T % 27] = v27.get(T % 27, 0) + 1
    c27 = {}
    for s, T in canon_T:
        c27[T % 27] = c27.get(T % 27, 0) + 1
    print(f"  violator T%27 top: {sorted(v27.items(), key=lambda x: -x[1])[:12]}")
    print(f"  canonical T%27 top: {sorted(c27.items(), key=lambda x: -x[1])[:12]}")
    canon27 = set(c27)
    viol_only = {r for r in v27 if r not in canon27}
    print(f"  residues mod 27 hit ONLY by violators: {sorted(viol_only)}")
    print(f"  residues mod 27 hit by canonical: {sorted(canon27)}")

def main():
    d_a()
    d_b()
    d_e()
    d_c()
    d_f()
    d_2()
    print("=" * 72)
    print("SEAM DISSECTION COMPLETE")

if __name__ == "__main__":
    main()
