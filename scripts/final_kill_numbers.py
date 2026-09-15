#!/usr/bin/env python3
# THE FINAL KILL — NUMBERS FIRST (ledger law: numbers before Lean, always)
# Phase 1: the worldtrace (mu-hat), the six dust candidates, the deep-band fire structure.

def trits(n, depth):
    """ternary trits of n up to depth"""
    t = []
    for _ in range(depth):
        t.append(n % 3)
        n //= 3
    return t

def L(s, mod):
    """L(s) = (4^(3^s) - 1) / 3^(s+1) mod `mod` (mod must be 3^m with m >= s+2)"""
    assert mod >= 3**(s+2), "need the quotient mod 3^m with m >= s+2 for exactness of low trits"
    return ((pow(4, 3**s, mod) - 1) // (3**(s+1))) % mod

DEPTH = 45   # 3-adic precision
MOD = 3**DEPTH

# ---------- 1. mu-hat: the frozen diagonal's trits ----------
# mu_hat's trits: trit_j(mu) = trit_j(L(j) mod 3^(j+2))  (stabilization depth j+1... use j+2 safe)
mu_trits = []
for j in range(DEPTH - 3):
    # L(j) is correct mod 3^(j+2) at least; read trits 0..j+1
    Lj = L(j, 3**(j+3))
    tj = trits(Lj, j+2)
    while len(mu_trits) < j+2 and len(tj) > len(mu_trits):
        mu_trits.append(tj[len(mu_trits)])
print("mu-hat trits (first 30):", mu_trits[:30])

# coherence check: L(s+1) ~ L(s) mod 3^(s+1)
ok = all(L(s, 3**(s+3)) % 3**(s+1) == L(s+1, 3**(s+3)) % 3**(s+1) for s in range(1, 30))
print("L stabilization coherent:", ok)

# ---------- 2. the six dust candidates ----------
# dust core: trit_j(core*mu) = 1 for all j >= 2;  t0 = core%3 in {1,2}, t1 = (7*core mod 9)/3
# candidate x = t0 + 3*t1 + sum_{j>=2} 3^j  (3-adic)
# 2*x = 2*t0 + 6*t1 - 9  =>  u = 2*t0 + 6*t1 - 9 in {-7,-5,-1,1,5,7}
# core_candidate = x * mu^{-1} (3-adic). Check eventual vanishing of trits (naturality).
def inv(a, mod):
    return pow(a, -1, mod)

print("\n--- the six dust candidates ---")
candidates = {}
for t0 in (1, 2):
    for t1 in (0, 1, 2):
        a = t0 + 3*t1
        u = 2*a - 9
        # x = a + sum_{j>=2} 3^j  mod 3^DEPTH = a + (3^DEPTH - 9)/2 -- careful: (3^DEPTH-9)/2 as integer
        x = (a + (3**DEPTH - 9)//2) % MOD
        mu = L(DEPTH - 3, MOD)   # mu mod 3^DEPTH (L(s) ~ mu mod 3^(s+1), s = DEPTH-3 -> mod 3^(DEPTH-2); refine below)
        # better: build mu at full depth by stabilization
        mu_full = 0
        for j in range(DEPTH):
            # trit j of mu from L(j) mod 3^(j+2)
            Lj = L(j, 3**(j+3))
            mu_full += (Lj % 3**(j+1)) - (mu_full % 3**(j+1)) if False else 0
        # simpler: mu mod 3^DEPTH via L(DEPTH-2) (correct mod 3^(DEPTH-1)); add one more level
        mu_approx = L(DEPTH-2, 3**DEPTH)  # correct mod 3^(DEPTH-1)
        core_cand = (x * inv(mu_approx, MOD)) % MOD
        ct = trits(core_cand, 30)
        # check eventual vanishing to depth 30
        tail_nonzero = [i for i in range(2, 30) if ct[i] != 0]
        eventually_zero = all(ct[i] == 0 for i in range(20, 30))
        candidates[(t0, t1)] = core_cand
        print(f"a={a} u={u:+d}  core_cand trits[0:16]={ct[:16]}  eventually_zero(20..30)={eventually_zero}")

# ---------- 3. the window/deep-band fire structure on REAL natural cores ----------
# For every three-free core, the diagonal D = core*mu (3-adic, trits t_j).
# Sheet S (K = 3^S * core): W_S = (4^(3^S*core)-1)/3^(S+1); trits of 4^K at pos >= S+1 = trits of W_S.
# Uniform kills: (a) t_j = 2 with j <= S -> frozen fire; (b) window: trit_{S+1}(W_S) = t_{S+1}+2 mod 3 fires iff t_{S+1}=0.
# Deep band: positions >= S+2 of W_S. Find WHERE natural cores actually fire deep.
def W_S_exact(core, S, mod):
    """W_S(core) mod 3^N via exact natural arithmetic"""
    e = 3**S * core
    return ((pow(4, e, mod*3**(S+1)) - 1) // 3**(S+1)) % mod

def digit3(x, p):
    return (x // 3**p) % 3

mu_full = L(40, 3**42)  # mu mod 3^41 (good to depth 41)
print("\n--- deep-band fire census (three-free cores 1..2000, sheets 1..6) ---")
deep_fire_positions = {}
for core in range(1, 2000):
    if core % 3 == 0: continue
    # diagonal trits t_j = trit_j(core*mu) to depth 24
    D = (core * mu_full) % 3**25
    t = trits(D, 25)
    first2 = next((j for j in range(25) if t[j] == 2), None)
    for S in range(1, 7):
        K = 3**S * core
        if K < 8: continue
        # killed by frozen (t_j=2, j<=S) or window (t_{S+1}=0)?
        frozen = first2 is not None and first2 <= S
        window = (S+1 < 25) and t[S+1] == 0
        if frozen or window: continue
        # survives uniform read -> where does W_S actually fire?
        N = 3**min(3*S+6, 24)
        W = W_S_exact(core, S, 3**24)
        fp = next((p for p in range(24) if digit3(W, p) == 2), None)
        key = (S, fp is not None and fp - (S+1))
        deep_fire_positions[key] = deep_fire_positions.get(key, 0) + 1
print("(sheet, deep-offset) counts  [offset = fire_pos - (S+1); None = no fire found in 24 trits]:")
for k in sorted(deep_fire_positions, key=lambda z: (z[0], -1 if z[1] is None else z[1])):
    print("  ", k, deep_fire_positions[k])

# ---------- 4. the act scan with mechanism classification ----------
print("\n--- act scan [8, 1200): mechanism classification ---")
mech = {"frozen": 0, "window": 0, "deep": 0, "below": 0}
for K in range(8, 1200):
    v = 0
    KK = K
    while KK % 3 == 0: KK //= 3; v += 1
    core = KK
    D = (core * mu_full) % 3**25
    t = trits(D, 25)
    S = v
    first2 = next((j for j in range(25) if t[j] == 2), None)
    if first2 is not None and first2 <= S:
        mech["frozen"] += 1
    elif S+1 < 25 and t[S+1] == 0:
        mech["window"] += 1
    else:
        W = W_S_exact(core, S, 3**24)
        fp = next((p for p in range(24) if digit3(W, p) == 2), None)
        if fp is None:
            mech["below"] += 1
        else:
            mech["deep"] += 1
            # record which offset
print(mech)
