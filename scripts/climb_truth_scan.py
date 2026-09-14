#!/usr/bin/env python3
# Truth-value scan of four_power_happy_climb (per repo defs):
#   digit3 n p = (n / 3^p) % 3
#   carry4 n p = (4 * (n % 3^p)) / 3^p
#   HappyCell C d := d = 2 ∧ (C = 0 ∨ C = 3)
#   climb := ∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)
# Carry recurrence (proved above): c_0 = 0, c_{p+1} = (4*d_p + c_p) // 3, and carry4 n p = c_p.
# Conjecture side: noTernaryTwo (4^K) = false  ⟺  some ternary digit of 4^K is 2.
import sys

def ternary_digits(n):
    ds = []
    while n > 0:
        n, r = divmod(n, 3)
        ds.append(r)
    return ds

def check(K):
    n = 4 ** K
    ds = ternary_digits(n)
    L = len(ds)
    conj = any(d == 2 for d in ds)          # conjecture holds at K
    climb = False
    first_p = None
    c = 0                                    # carry into position 0 = carry4 n 0
    for p in range(L):
        d = ds[p]
        if d == 2 and c in (0, 3):
            if p >= 3:
                climb = True
                if first_p is None:
                    first_p = (p, c)
        c = (4 * d + c) // 3
    return conj, climb, first_p, L

def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    fails = []          # K where climb FALSE
    conj_fails = []     # K where conjecture FALSE (digit-2 missing)
    sep = []            # K where conjecture TRUE but climb FALSE (climb strictly stronger)
    for K in range(lo, hi + 1):
        conj, climb, fp, L = check(K)
        if not conj:
            conj_fails.append(K)
        if not climb:
            fails.append(K)
            if K >= 8 and conj:
                sep.append(K)
        if K % 500 == 0:
            print(f"progress K={K} len={L} first_happy={fp}", flush=True)
    print("=== SCAN DONE", lo, hi, "===")
    print("climb FALSE at K:", fails[:50], "..." if len(fails) > 50 else "", "total", len(fails))
    print("conjecture FALSE at K:", conj_fails[:50], "total", len(conj_fails))
    print("climb-false-but-conjecture-true (kill witnesses, K>=8):", sep[:50], "total", len(sep))

main()
