#!/usr/bin/env python3
"""
Erdos-Graham / Erdos Problem #261 — the greedy walk engine.

THE WALK (decoded from Tengely-Ulas-Zygadlo 2020, arXiv:2008.01501):
  state (N, v):  v = (remaining value) * 2^(N-1),  invariant 0 <= v < N+1
  start: (N, v) = (n+1, n)      [for n >= 2]
  step: if 2v >= N: TAKE piece N:  v <- 2v - N ; else v <- 2v ;  N <- N+1
  i.e. v_{N+1} = (2 * v_N) mod N
  TERMINATION: v hits 0  <=>  greedy closes  <=>  n/2^n = sum_{a in S} a/2^a,
  with S = set of taken indices, a_1 = n+1, |S| = k >= 2.

Verify: (a) reproduces BL family, (b) matches TUZ20 n <= 10^4,
(c) extend verification + exact witnesses.
"""
import sys

def greedy_walk(n, max_steps=50_000_000):
    """Return (S, steps) with S the witness list, or None if not terminated."""
    if n == 1:
        N, v = 3, 2
    else:
        N, v = n + 1, n
    S = []
    steps = 0
    while v > 0 and steps < max_steps:
        if 2 * v >= N:
            S.append(N)
            v = 2 * v - N
        else:
            v = 2 * v
        N += 1
        steps += 1
    if v == 0:
        return S, steps
    return None, steps

def verify_witness(n, S):
    """Exact integer check: sum_{a in S} a/2^a == n/2^n, |S| >= 2, strictly increasing."""
    if len(S) < 2:
        return False
    if any(S[i] >= S[i+1] for i in range(len(S)-1)):
        return False
    M = max(S)
    # scale by 2^M: sum a * 2^(M-a) == n * 2^(M-n)
    lhs = sum(a << (M - a) for a in S)
    rhs = n << (M - n)
    return lhs == rhs

def main():
    limit = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000
    out = open('walk_witnesses.tsv', 'w')
    fails = []
    stats = []
    for n in range(1, limit + 1):
        S, steps = greedy_walk(n)
        if S is None:
            fails.append(n)
            out.write(f"{n}\tTIMEOUT\t{steps}\n")
            continue
        if not verify_witness(n, S):
            fails.append(n)
            out.write(f"{n}\tBADWITNESS\t{S}\n")
            continue
        k = len(S)
        ak = S[-1]
        stats.append((n, k, ak, steps))
        out.write(f"{n}\t{k}\t{ak}\t{steps}\t{S}\n")
    out.close()
    print(f"verified n <= {limit}: {limit - len(fails)} PASS, {len(fails)} FAIL")
    if fails:
        print("failures:", fails[:20])
    # conjecture check: a_k <= 2(n + k)  (TUZ20's conjecture, true for n >= 2k - k)
    viol = [(n,k,ak) for (n,k,ak,_) in stats if ak > 2*(n+k)]
    print(f"violations of a_k <= 2(n+k): {len(viol)}")
    if viol: print("first:", viol[:10])
    # growth stats
    import statistics
    aks = [ak for (_,_,ak,_) in stats]
    ks = [k for (_,k,_,_) in stats]
    print(f"max a_k: {max(aks)} (n={stats[aks.index(max(aks))][0]}), max k: {max(ks)}")
    # ratio a_k/n distribution
    rs = sorted(ak/n for (n,_,ak,_) in stats if n >= 100)
    print(f"a_k/n quantiles (n>=100): min {rs[0]:.3f}, med {rs[len(rs)//2]:.3f}, max {rs[-1]:.3f}")

if __name__ == '__main__':
    main()
