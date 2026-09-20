#!/usr/bin/env python3
"""SEAM DISSECTION PART 2 — the two-zone transport law.

Green base discovered in part 1:
  D-B: Navigation (lteCoeff s) holds for ALL s >= 2
       (s=2: row 4 carry 3; s=3: row 7 carry 0; s>=4: row 4 carry 0 via lteCoeff s = 178 mod 243)
  D-D: lteCoeff (s+1) = lteCoeff s mod 3^(s+1)  (cube-lift stabilization, Lean-provable)

This part dissects the TRANSPORT: parent tail = 1 + 3*(z_s + T) + 3^(s+2)*(u_s*T) exactly,
where T = child tail, z_s = prefixOffset s, u_s = lteCoeff s (since 4^(3^s) = 1 + 3^(s+1)*lteCoeff s).
  Zone 1 (rows 0..s+1): digits of 1 + 3*(z_s + T mod 3^(s+1))
  Zone 2 (rows s+2..):  digits of (T/3^(s+1) + u_s*T)
"""
import random

def digit3(X, p):
    return (X // 3 ** p) % 3

def carry4(X, p):
    return 4 * (X % 3 ** p) // 3 ** p

def happy(C, d):
    return d == 2 and C in (0, 3)

def tail_mod(s, b, J):
    m = 3 ** (s + 1 + J)
    v = pow(4, (3 ** s) * b, m)
    return ((v - 1) // 3 ** (s + 1)) % (3 ** J)

def nav_happy_rows(Xmod, J):
    out = []
    for p in range(J):
        d = (Xmod // 3 ** p) % 3
        c = 4 * (Xmod % 3 ** p) // 3 ** p
        if happy(c, d):
            out.append((p, d, c))
    return out

def v3(x):
    if x == 0:
        return 10 ** 9
    v = 0
    while x % 3 == 0:
        v += 1
        x //= 3
    return v

# ---------- T1: exact two-zone decomposition sanity + witness-zone census ----------

def t1():
    print("=" * 72)
    print("T1  EXACT TWO-ZONE DECOMPOSITION + witness-zone census (s in 1..5, n in 1..120)")
    J = 90
    sanity_ok = True
    zone1 = zone2 = 0
    dq_hist = {}
    for s in range(1, 6):
        z = tail_mod(s, 1, J + 2) // 3               # prefixOffset s mod 3^J  (need /3 exact mod)
        u = tail_mod(s, 1, J)                        # lteCoeff s mod 3^J
        for n in range(1, 121):
            T = tail_mod(s + 1, n, J + s + 2)        # child tail mod 3^(J+s+2) for exact zone algebra
            Tl = T % 3 ** (s + 1)                    # low part
            Th = T // 3 ** (s + 1)                   # high part
            P = (1 + 3 * (z + Tl) + 3 ** (s + 2) * (Th + u * T)) % 3 ** J
            Ptrue = tail_mod(s, 1 + 3 * n, J)
            if P != Ptrue:
                sanity_ok = False
                if n <= 3:
                    print(f"  ZONE SANITY FAIL s={s} n={n}")
            hp = nav_happy_rows(Ptrue, J)
            hq = nav_happy_rows(T % 3 ** J, J)
            if hp and hq:
                pmin, qmin = hp[0][0], hq[0][0]
                dq_hist[qmin - pmin] = dq_hist.get(qmin - pmin, 0) + 1
                if pmin <= s + 1:
                    zone1 += 1
                else:
                    zone2 += 1
    print(f"  two-zone decomposition EXACT: {'HOLDS' if sanity_ok else 'FAILS'}")
    print(f"  parent minimal witness in zone 1 (rows <= s+1): {zone1}; zone 2: {zone2}")
    print(f"  child-row minus parent-row (q*-p*) histogram: {dict(sorted(dq_hist.items()))}")

# ---------- T2: transport table for the m-families (s=1..3) ----------

def t2():
    print("=" * 72)
    print("T2  TRANSPORT TABLE: n = 3^k * m; child q*, parent p*, zone, carry")
    J = 120
    for s in range(1, 4):
        for m in [1, 2, 4, 5, 7, 8, 10, 11, 13, 14, 16, 17]:
            if m % 3 == 0:
                continue
            line = []
            for k in range(1, 7):
                n = (3 ** k) * m
                Q = tail_mod(s + 1, n, J)
                P = tail_mod(s, 1 + 3 * n, J)
                hq = nav_happy_rows(Q, J)
                hp = nav_happy_rows(P, J)
                q = hq[0] if hq else None
                p = hp[0] if hp else None
                line.append((k, q[0] if q else None, q[2] if q else None,
                             p[0] if p else None, p[2] if p else None))
            print(f"  s={s} m={m:2d}: " + "  ".join(
                f"k{k}:q{q}c{c}->p{p}c{pc}" for k, q, c, p, pc in line))

# ---------- T3: the m=1, m=4 exact law across s ----------

def t3():
    print("=" * 72)
    print("T3  m=1 FAMILY EXACT LAW: child = 3^k * lteCoeff(s+k+1); p*(s,k) = ?")
    J = 120
    print("  (s, k) -> child q* (theory: happy(lteCoeff(s+k+1)) + k), parent p*")
    for s in range(1, 7):
        row = []
        for k in range(1, 8):
            n = 3 ** k
            Q = tail_mod(s + 1, n, J)
            P = tail_mod(s, 1 + 3 * n, J)
            hq = nav_happy_rows(Q, J)
            hp = nav_happy_rows(P, J)
            q = hq[0][0] if hq else None
            p = hp[0][0] if hp else None
            # theory: child = 3^k * canonicalTail(s+k+1, 1)?? verify:
            th = 3 ** k * tail_mod(s + 1 + k - 1 + 1, 1, J)  # placeholder, verified below
            row.append(f"k={k}: q={q} p={p}")
        print(f"  s={s}: " + "  ".join(row))
    print("  verify child = 3^k * lteCoeff(s+k+1):")
    for s in range(1, 6):
        for k in range(1, 7):
            n = 3 ** k
            Q = tail_mod(s + 1, n, J + k)
            L = tail_mod(s + 1 + k, 1, J)
            if Q % 3 ** J != (3 ** k * L) % 3 ** J:
                print(f"    s={s} k={k}: CHILD-UNIT-SHIFT FAILS")
                return
    print("    HOLDS for all s in 1..5, k in 1..6")

# ---------- T4: stabilization of the transport operator ----------

def t4():
    print("=" * 72)
    print("T4  TRANSPORT OPERATOR STABILIZATION: z_s = prefixOffset s, u_s = lteCoeff s mod 3^j")
    for j in (2, 3, 4, 5, 6):
        vals = {}
        for s in range(1, 18):
            z = tail_mod(s, 1, j + 2) // 3
            u = tail_mod(s, 1, j)
            vals.setdefault((z % 3 ** j, u % 3 ** j), []).append(s)
        stable = [v for v in vals.values() if len(v) >= 8 and max(v) - min(v) >= 6]
        print(f"  mod 3^{j}: distinct (z,u) pairs: {len(vals)}; "
              f"long-lived stable pair s-range: {stable[:3]}")

# ---------- T5: fire vs happy + quarter law ----------

def t5():
    print("=" * 72)
    print("T5  FIRE-VS-HAPPY + CARRY QUARTER LAW on canonical parent tails")
    J = 120
    tot = happy_at_fire = 0
    qcnt = {0: 0, 1: 0, 2: 0}
    for s in range(1, 5):
        for n in range(1, 121):
            X = tail_mod(s, 1 + 3 * n, J)
            for p in [p for p in range(J) if digit3(X, p) == 2][:4]:
                c = carry4(X, p)
                tot += 1
                if c in (0, 3):
                    happy_at_fire += 1
                r = (X % 3 ** p) / (3 ** p) if 3 ** p < 10 ** 15 else 0.5
                if r < 0.25:
                    qcnt[0] += 1
                elif r > 0.75:
                    qcnt[2] += 1
                else:
                    qcnt[1] += 1
    print(f"  first-4 fire rows per tail: {tot}; carry in (0,3): "
          f"{happy_at_fire} ({100*happy_at_fire/max(tot,1):.1f}%)")
    print(f"  window quarter at fire rows: bottom={qcnt[0]} middle={qcnt[1]} top={qcnt[2]}")

# ---------- T6: violator separator (from part 1, D-2) ----------

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

def t6():
    print("=" * 72)
    print("T6  VIOLATOR SEPARATOR: forced-prefix random-T WCP violators vs canonical T")
    random.seed(11)
    viol_T = []
    for _ in range(25000):
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
            if w > 0:
                viol_T.append((s, T))
    canon_T = []
    for s in range(1, 4):
        for n in range(1, 61):
            canon_T.append((s, tail_mod(s + 1, n, 12)))
    print(f"  violators: {len(viol_T)}; canonical samples: {len(canon_T)}")
    v27 = {}
    for s, T in viol_T:
        v27[T % 27] = v27.get(T % 27, 0) + 1
    c27 = {}
    for s, T in canon_T:
        c27[T % 27] = c27.get(T % 27, 0) + 1
    print(f"  violator T%27 histogram: {dict(sorted(v27.items()))}")
    print(f"  canonical T%27 histogram: {dict(sorted(c27.items()))}")
    canon27 = set(c27)
    viol_only = sorted({r for r in v27 if r not in canon27})
    both = sorted({r for r in v27 if r in canon27})
    print(f"  residues hit ONLY by violators: {viol_only}")
    print(f"  residues hit by BOTH: {both}")
    print(f"  residues hit ONLY by canonical: {sorted(set(c27) - set(v27))}")
    # deeper: mod 81 on the overlapping band
    v81 = {}
    for s, T in viol_T:
        if T % 27 in canon27:
            v81[T % 81] = v81.get(T % 81, 0) + 1
    c81 = {}
    for s, T in canon_T:
        if T % 27 in canon27:
            c81[T % 81] = c81.get(T % 81, 0) + 1
    print(f"  within overlap, violator T%81: {dict(sorted(v81.items())[:20])}")
    print(f"  within overlap, canonical T%81: {dict(sorted(c81.items())[:20])}")

def main():
    t1()
    t2()
    t3()
    t4()
    t5()
    t6()
    print("=" * 72)
    print("PART 2 COMPLETE")

if __name__ == "__main__":
    main()
