#!/usr/bin/env python3
# Round 3: verify (a) trinomial read on randoms, (b) six-point congruence on the candidates,
# (c) the candidates' W_S fire scan (dust emptiness), (d) act mechanism census (corrected).

import random
random.seed(406)

def trits(n, depth):
    t = []
    for _ in range(depth):
        t.append(n % 3); n //= 3
    return t

def Lmod(s, m):
    M = 3**(s+1+m)
    return ((pow(4, 3**s, M) - 1) // 3**(s+1)) % (3**m)

def digit3(x, p): return (x // 3**p) % 3
def inv(a, mod): return pow(a, -1, mod)

D = 40
mu_full = Lmod(36, 38)          # mu mod 3^38
MOD = 3**38

def W_exact(core, S, N):
    e = 3**S * core
    M = 3**(S+1+N)
    return ((pow(4, e, M) - 1) // 3**(S+1)) % (3**N)

def C(n, k): return n*(n-1)*(n-2)//6 if k == 3 else (n*(n-1)//2 if k == 2 else None)

# ---------- (a) trinomial read on randoms ----------
ok_count, tot = 0, 0
for _ in range(400):
    core = random.randrange(1, 5000)
    S = random.randrange(0, 7)
    N = min(3*S+3, 20)
    L = Lmod(S, N+2) if S < 30 else None
    if L is None: continue
    W = W_exact(core, S, N)
    Q = (core*L + 3**(S+1)*C(core,2)*L*L + 3**(2*S+2)*C(core,3)*(L**2)*L) % (3**N)
    tot += 1
    if W == Q: ok_count += 1
print(f"(a) trinomial read: {ok_count}/{tot} exact matches")

# ---------- (b) six-point congruence on the candidates ----------
print("\n(b) six-point congruence (candidate cores):")
for a in (1, 2, 4, 5, 7, 8):
    x = (a + (MOD - 9)//2) % MOD
    core_cand = (x * inv(mu_full, MOD)) % MOD
    u = 2*a - 9
    oks = []
    for k in range(3, 25):
        Lk = Lmod(k-1, k+2)
        lhs = (2 * core_cand % MOD * Lk) % (3**k)
        rhs = u % (3**k)
        oks.append(lhs == rhs)
    print(f"  a={a} u={u:+d}: 2*core*L(k-1) = u mod 3^k for all k in [3,25): {all(oks)}")

# ---------- (c) the candidates' W_S fire scan (dust emptiness check) ----------
# W_S(candidate) via the exp series with correct inverse factorials:
#   W_S = sum_i 3^((i-1)(S+1)) * D^i / i!,   D = candidate core * mu  (= x = a - 9/2)
def W_exp_3adic(x, S, N):
    total = 0
    for i in range(1, 3*N):
        sh = (i-1)*(S+1)
        vi = 0; unit = 1
        for j in range(2, i+1):
            jj = j
            while jj % 3 == 0: vi += 1; jj //= 3
            unit = unit * jj
        if sh - vi >= N: break
        if sh < vi: continue
        term = pow(x, i, 3**N) * inv(unit % (3**N), 3**N) % (3**N)
        term = term * pow(3, sh-vi, 3**N) % (3**N)
        total = (total + term) % (3**N)
    return total

# validate the exp-series engine against exact W on natural cores first
print("\n(c0) exp-series engine validation (natural cores):")
for core, S in [(4,1),(1,1),(5,2),(7,1),(13,2),(2,3),(26,1)]:
    we = W_exact(core, S, 18)
    Dv = (core * mu_full) % MOD
    wx = W_exp_3adic(Dv, S, 18)
    print(f"  core={core} S={S}: match={we == wx}")

print("\n(c) candidates' W_S fire scan (first fire trit position in W_S):")
for a in (1, 2, 4, 5, 7, 8):
    x = (a + (MOD - 9)//2) % MOD
    fires = []
    for S in range(0, 10):
        W = W_exp_3adic(x, S, 3*S+8 if 3*S+8 < 30 else 30)
        fp = next((p for p in range(len(trits(W, 30))) if digit3(W, p) == 2), None)
        fires.append(fp)
    print(f"  a={a}: W_S fire trits for S=0..9: {fires}")

# ---------- (d) act mechanism census (corrected, full print) ----------
from collections import Counter
mech = Counter()
examples_deep = []
for K in range(8, 1200):
    v, KK = 0, K
    while KK % 3 == 0: KK //= 3; v += 1
    core, S = KK, v
    Dv = (core * mu_full) % (3**25)
    t = trits(Dv, 25)
    first2 = next((j for j in range(25) if t[j] == 2), None)
    if first2 is not None and first2 <= S: mech["frozen"] += 1
    elif S+1 < 25 and t[S+1] == 0: mech["window"] += 1
    else:
        W = W_exact(core, S, 24)
        fp = next((p for p in range(24) if digit3(W, p) == 2), None)
        if fp is None: mech["NOFIRE"] += 1
        else:
            mech["deep"] += 1
            if len(examples_deep) < 12: examples_deep.append((K, core, S, fp))
print("\n(d) act mechanisms [8,1200):", dict(mech))
print("    deep examples (K, core, S, W-fire-trit):", examples_deep)
