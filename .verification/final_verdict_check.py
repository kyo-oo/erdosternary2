#!/usr/bin/env python3
"""Reproduction script for THE_FINAL_VERDICT.md receipts (§4, §5).

Run: python3 .verification/final_verdict_check.py
Runtime: a few minutes (pure Python bignum arithmetic).
"""
import random


def digit3(X, p):
    return (X // 3 ** p) % 3


def carry4(X, p):
    return 4 * (X % 3 ** p) // 3 ** p


def happy(C, d):
    return d == 2 and C in (0, 3)


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
    return (dP[outDigit(C, d)] - 4 * dP[d] + cP[C]
            - 3 * cP[nextCarry(C, d)] + 84 * surviveI(C, d))


CERT = {(0, 0): -57, (0, 1): -111, (0, 2): 105, (1, 0): -39, (1, 1): -81,
        (1, 2): -84, (2, 0): -111, (2, 1): -93, (2, 2): 0,
        (3, 0): 0, (3, 1): 0, (3, 2): 105}


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
    for t in range(N):
        for p in range(W - 1):
            assert D[t + 1][p] == outDigit(C[t][p], D[t][p])
            assert C[t][p + 1] == nextCarry(C[t][p], D[t][p])
    return C, D


def main():
    assert all(CD(*k) == v for k, v in CERT.items())
    print("crossDensity table == certified table: OK")

    random.seed(42)
    viol = tot = 0
    for _ in range(40000):
        N = random.randint(2, 7)
        b = random.randint(0, 3)
        K = random.randint(2, 6)
        E = random.randint(0, 3 ** (b + K + 2) - 1)
        C, D = rectangle(E, N, b, K)
        if all(not happy(C[N][b + j], D[N][b + j]) for j in range(K)):
            tot += 1
            if WCP([[C[t][b + i] for i in range(K)] for t in range(N + 1)],
                   [[D[t][b + i] for i in range(K)] for t in range(N + 1)],
                   N, K) > 0:
                viol += 1
    print(f"WCP lemma, general rectangles: {viol}/{tot} violations"
          f" ({100*viol/max(tot,1):.1f}%)  [verdict doc: 4119/18829 = 21.9%]")

    random.seed(7)
    viol = tot = 0
    for _ in range(60000):
        s = random.randint(1, 3)
        N = 3 ** s
        b = s + 2
        K = random.randint(2, 7)
        T = random.randint(0, 3 ** (K + 2) - 1)
        E = 1 + (3 ** b) * T
        C, D = rectangle(E, N, b, K)
        if all(not happy(C[N][b + j], D[N][b + j]) for j in range(K)):
            tot += 1
            if WCP([[C[t][b + i] for i in range(K)] for t in range(N + 1)],
                   [[D[t][b + i] for i in range(K)] for t in range(N + 1)],
                   N, K) > 0:
                viol += 1
    print(f"WCP lemma, forced-prefix rectangles: {viol}/{tot} violations"
          f" ({100*viol/max(tot,1):.1f}%)  [verdict doc: 7556/31246 = 24.2%]")

    bad = vac = 0
    for s in range(1, 4):
        for n in range(1, 41):
            T = 4 ** (3 ** (s + 1) * n) // 3 ** (s + 2)
            P = 4 ** (3 ** s * (1 + 3 * n))
            navChild = any(happy(carry4(T, q), digit3(T, q))
                           for q in range(400))
            if navChild:
                if not any(happy(carry4(P, p), digit3(P, p))
                           for p in range(s + 2, 400)):
                    bad += 1
            else:
                vac += 1
    print(f"Collision theorem, s in 1..3 x n in 1..40: {bad} failures,"
          f" {vac} vacuous  [verdict doc: 0 / 0]")

    fail = [n for n in range(9, 1201)
            if not any(digit3(2 ** n, p) == 2 for p in range(0, 2 * n))]
    print(f"Erdos ternary-2, n in [9,1200]: {len(fail)} failures"
          f"  [verdict doc: 0]")


if __name__ == "__main__":
    main()
