#!/usr/bin/env python3
# THE FINAL KILL — NUMBERS, round 2 (bug fixed: L(s) mod 3^m needs 4^(3^s) mod 3^(s+1+m))

def trits(n, depth):
    t = []
    for _ in range(depth):
        t.append(n % 3)
        n //= 3
    return t

def Lmod(s, m):
    """L(s) = (4^(3^s)-1)/3^(s+1) mod 3^m  (exact: needs 4^(3^s) mod 3^(s+1+m))"""
    M = 3**(s+1+m)
    return ((pow(4, 3**s, M) - 1) // 3**(s+1)) % (3**m)

DEPTH = 42

# ---------- 1. mu-hat trits ----------
mu_trits = []
for j in range(DEPTH - 2):
    Lj = Lmod(j, j+3)          # L(j) correct mod 3^(j+3)
    tj = trits(Lj, j+3)
    for k in range(len(tj)):
        if len(mu_trits) <= k:
            mu_trits.append(tj[k])   # trit k frozen at level j >= k-... (safe: j+3 > k)
print("mu-hat trits (first 24):", mu_trits[:24])

# coherence: L(s+1) ~ L(s) mod 3^(s+1)
ok = all(Lmod(s, s+3) % 3**(s+1) == Lmod(s+1, s+3) % 3**(s+1) for s in range(1, 30))
print("L stabilization coherent:", ok)

# full mu mod 3^DEPTH
mu_full = Lmod(DEPTH-3, DEPTH-2+1)   # L(DEPTH-3) correct mod 3^(DEPTH-2) -> refine: use deeper
mu_full = Lmod(38, 40)               # mod 3^40
MOD = 3**40
assert (mu_full * 1) % 3 == 1

# ---------- 2. the six dust candidates (with correct mu) ----------
def inv(a, mod): return pow(a, -1, mod)
print("\n--- the six dust candidates (corrected) ---")
for t0 in (1, 2):
    for t1 in (0, 1, 2):
        a = t0 + 3*t1
        u = 2*a - 9
        x = (a + (MOD - 9)//2) % MOD          # x = a - 9/2 (3-adic) mod 3^40
        core_cand = (x * inv(mu_full, MOD)) % MOD
        ct = trits(core_cand, 30)
        eventually_zero = all(ct[i] == 0 for i in range(20, 30))
        print(f"a={a} u={u:+d}  core_cand trits[0:16]={ct[:16]}  ev_zero={eventually_zero}")

# ---------- 3. exp-series validation: W_S via 3-adic exp series vs exact ----------
def W_exp(core, S, N):
    """W_S(core) mod 3^N via the exp series  sum_i 3^((i-1)(S+1)) D^i / i!  with D = core*mu"""
    D = (core * mu_full) % (3**N)
    total = 0
    for i in range(1, 2*N+2):
        # term = 3^((i-1)(S+1)) * D^i / i!
        # v_3(i!) <= i/2; need (i-1)(S+1) - v3(i!) >= N to stop
        sh = (i-1)*(S+1)
        vi = 0; f = 1
        for j in range(2, i+1):
            jj = j
            while jj % 3 == 0: vi += 1; jj //= 3
        if sh - vi >= N: break
        # D^i / i! = D^i * 3^{-vi} * (unit part) -- compute 3-adically:
        # term = 3^(sh-vi) * (D^i * unit(i!)) mod 3^N where unit(i!) = i!/3^vi
        unit = 1
        for j in range(2, i+1):
            jj = j
            while jj % 3 == 0: jj //= 3
            unit = (unit * jj)
        term = (pow(D, i, 3**N) * unit) % (3**N)
        term = (term * pow(3, sh - vi, 3**N)) % (3**N) if sh >= vi else None
        if term is None: continue
        total = (total + term) % (3**N)
    return total

def W_exact(core, S, N):
    e = 3**S * core
    M = 3**(S+1+N)
    return ((pow(4, e, M) - 1) // 3**(S+1)) % (3**N)

print("\n--- exp-series validation ---")
for core, S in [(4,1),(1,1),(5,2),(7,1),(13,2),(2,3)]:
    we = W_exact(core, S, 20)
    wx = W_exp(core, S, 20)
    print(f"core={core} S={S}: exact==expseries: {we == wx}  (W mod 3^20 = {we})")

# ---------- 4. CLEAN census: correct diagonal trits, exact deep fires ----------
def digit3(x, p): return (x // 3**p) % 3
print("\n--- clean deep-band census (three-free cores 1..3000, sheets 1..7) ---")
from collections import Counter
census = Counter()
survivors = []
for core in range(1, 3000):
    if core % 3 == 0: continue
    D = (core * mu_full) % (3**25)
    t = trits(D, 25)
    first2 = next((j for j in range(25) if t[j] == 2), None)
    for S in range(1, 8):
        K = 3**S * core
        if K < 8: continue
        frozen = first2 is not None and first2 <= S
        window = (S+1 < 25) and t[S+1] == 0
        if frozen or window: continue
        W = W_exact(core, S, 3**0 if False else 24) if False else W_exact(core, S, 24)
        fp = next((p for p in range(24) if digit3(W, p) == 2), None)
        census[(S, None if fp is None else fp-(S+1))] += 1
        if fp is None or fp - (S+1) >= 2:
            survivors.append((core, S, fp))
print("(sheet, offset) counts:")
for k in sorted(census, key=lambda z: (z[0], 99 if z[1] is None else z[1])):
    print("  ", k, census[k])
print("deep-offset >= 2 or no-fire cases (first 25):", survivors[:25])

# ---------- 5. act scan with correct mechanisms ----------
print("\n--- act scan [8, 1200): correct mechanism classification ---")
mech = Counter()
for K in range(8, 1200):
    v, KK = 0, K
    while KK % 3 == 0: KK //= 3; v += 1
    core = KK; S = v
    D = (core * mu_full) % (3**25)
    t = trits(D, 25)
    first2 = next((j for j in range(25) if t[j] == 2), None)
    if first2 is not None and first2 <= S: mech["frozen"] += 1
    elif S+1 < 25 and t[S+1] == 0: mech["window"] += 1
    else:
        W = W_exact(core, S, 24)
        fp = next((p for p in range(24) if digit3(W, p) == 2), None)
        mech["deep" if fp is not None else "NOFIRE"] += 1
print(dict(mech))
