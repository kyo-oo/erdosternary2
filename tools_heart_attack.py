#!/usr/bin/env python3
# THE HEART ATTACK v2 — GAP-A2/GAP-A1 unified numerics (bounded, exact big-int, no floats)
# ALL tower arithmetic MODULAR (no astronomical ints). Machine receipts for DERIVATION_E_DUST_EMPTY.md
import sys

def digits3(n, j):
    return (n // (3 ** j)) % 3

def fire_row(K, max_row=80):
    for j in range(1, max_row + 1):
        m = 3 ** (j + 1)
        if (pow(4, K, m) // (3 ** j)) % 3 == 2:
            return j
    return None

def trits(n, count):
    return [(n // (3 ** j)) % 3 for j in range(count)]

def v_of(K):
    v = 0
    while 3 ** (v + 1) <= K:
        v += 1
    return v

def c_mod(t, prec):
    """c_t mod 3^prec, computed modularly: c_t = (4^(3^t)-1)/3^(t+1)."""
    M = 3 ** (t + 1 + prec)
    A = pow(4, 3 ** t, M)
    return ((A - 1) // (3 ** (t + 1))) % (3 ** prec)

PREC = 26

print("=" * 70)
print("SECTION 1: THE c-TOWER AND c_INFTY (modular, exact)")
print("=" * 70)
c_full = [None]  # exact ints for small t (for formula checks)
for t in range(0, 8):
    c_full.append((4 ** (3 ** t) - 1) // (3 ** (t + 1)))
# note: c_full[t] uses index t; c_full[0] is placeholder
c_exact = {t: (4 ** (3 ** t) - 1) // (3 ** (t + 1)) for t in range(0, 8)}
# stabilization: c_{t+1} = c_t mod 3^(t+1), modularly
stab_ok = 0
for t in range(0, 26):
    a = c_mod(t, t + 2)
    b = c_mod(t + 1, t + 2)
    if (b - a) % (3 ** (t + 1)) == 0:
        stab_ok += 1
print(f"  c_(t+1) = c_t mod 3^(t+1) for t in [0,26): {stab_ok}/26 PASS")
# cross-check modular vs exact for small t
okx = all(c_mod(t, 20) == c_exact[t] % (3 ** 20) for t in range(8))
print(f"  modular c_t matches exact c_t mod 3^20 (t<8): {okx}")
cinf = c_mod(26, PREC)
cinf_trits = trits(cinf, 24)
print(f"  c_0={c_exact[0]}, c_1={c_exact[1]}, c_2={c_exact[2]}, c_3 mod 81={c_mod(3,4)%81}")
print(f"  c_infty trits (pos 0..23): {cinf_trits}")
twos = [i for i, d in enumerate(cinf_trits) if d == 2]
print(f"  2-positions of c_infty (first 24): {twos}")
ok79 = all(c_mod(t, 2) % 9 == 7 for t in range(1, 27))
ok1681 = all(c_mod(t, 4) % 81 == 16 for t in range(3, 27))
print(f"  c_t = 7 mod 9 for t in [1,27): {ok79}")
print(f"  c_t = 16 mod 81 for t in [3,27): {ok1681}")

print()
print("=" * 70)
print("SECTION 2: MULTIPLICATIVE TOWER-FACTORIZATION (exact identity check, small K)")
print("=" * 70)
import random
random.seed(12345)
def tower_factorize(K):
    n = 1; KK = K; t = 0
    while KK > 0:
        tr = KK % 3
        if tr:
            n *= (4 ** (3 ** t)) ** tr
        KK //= 3; t += 1
    return n
ok = sum(1 for _ in range(200) if tower_factorize(K := random.randrange(0, 3000)) == 4 ** K)
print(f"  4^K = Prod_t 4^(3^t)^trit_t(K): {ok}/200 random K in [0,3000) EXACT")

print()
print("=" * 70)
print("SECTION 3: BLADE ORDER 5 — period and structure on the dust path")
print("=" * 70)
def blade(m, j):
    mod = 3 ** (j + 1)
    return (pow(4, 1 + 3 * m, mod) // (3 ** j)) % 3
f5 = [blade(m, 5) for m in range(729)]
ok243 = all(f5[m] == f5[m + 243] == f5[m + 486] for m in range(243))
smaller = None
for p in [1, 3, 9, 27, 81]:
    if all(f5[m] == f5[m + p] for m in range(729 - p)):
        smaller = p; break
print(f"  B_5 period 243 (m, m+243, m+486 equal, m<243): {ok243}; smaller period: {smaller}")
corr = {}
okform = True
for m in range(729):
    t3 = (m // 81) % 3
    key = m % 81
    if key not in corr:
        corr[key] = (f5[m] - t3) % 3
    elif (f5[m] - t3) % 3 != corr[key]:
        okform = False
print(f"  B_5(m) = (trit_3(m) + corr(m mod 81)) % 3, corr well-defined: {okform}")
if okform:
    nz = {k: v for k, v in corr.items() if v != 0}
    print(f"  nonzero corr entries (m mod 81 -> corr): {nz}")
    cantor81 = [r for r in range(81) if all((r // (3**i)) % 3 in (0, 1) for i in range(4))]
    act = [r for r in cantor81 if corr[r] != 0]
    print(f"  Cantor residues mod 81: {len(cantor81)}; ACTIVE on Cantor path: {act}")
    print(f"  their corr values: { {r: corr[r] for r in act} }")

print()
print("=" * 70)
print("SECTION 4: DUST TREE vs PURE CANTOR — deviation map (blade activation)")
print("=" * 70)
for L in range(1, 9):
    dust = []
    for r in range(3 ** L):
        clean = True
        for j in range(1, L + 1):
            if digits3(pow(4, r, 3 ** (j + 1)), j) == 2:
                clean = False; break
        if clean:
            dust.append(r)
    tf = [r for r in dust if r % 3 == 1]
    sh = [r for r in dust if r % 3 == 0]
    pc = []
    for r in tf:
        m = (r - 1) // 3
        if all(((m // (3 ** i)) % 3) in (0, 1) for i in range(L - 1)):
            pc.append(r)
    dev = sorted(set(tf) - set(pc))
    print(f"  L={L}: dust={len(dust)} (2^(L-1)={2**(L-1)}), three-free={len(tf)}, sheets={len(sh)}")
    if L <= 7:
        print(f"       tf dust: {tf}")
        print(f"       DEVIATIONS from pure Cantor: {dev}")

print()
print("=" * 70)
print("SECTION 5: KILL-ROW GEOMETRY vs the window (v = floor(log3 K))")
print("=" * 70)
stats = {}
maxrow = (0, None)
nododge = 0
dust_window = []
for K in range(8, 100001):
    fr = fire_row(K, 60)
    if fr is None:
        print(f"  !! K={K} no fire up to row 60"); continue
    v = v_of(K)
    stats[fr - (2 * v + 1)] = stats.get(fr - (2 * v + 1), 0) + 1
    if fr > maxrow[0]:
        maxrow = (fr, K)
    if fr > 2 * v + 1:
        nododge += 1
        dust_window.append((K, fr, v))
print(f"  K in [8,100000]: all fire; max row {maxrow[0]} at K={maxrow[1]}")
print(f"  (fire_row - (2v+1)) histogram: {sorted(stats.items(), key=lambda x: -x[1])[:12]}")
print(f"  window-dodgers (fire beyond 2v+1): {nododge}")
print(f"  first 15 dodgers (K, fire_row, v): {dust_window[:15]}")

print()
print("=" * 70)
print("SECTION 6: WINDOW READ LAW — prefaced object match (green law check, modular)")
print("=" * 70)
okw = badw = 0
for K in range(9, 3000):
    v = v_of(K)
    if v < 1: continue
    u = K // (3 ** v); r = K % (3 ** v)
    if u == 0: continue
    J = 2 * v + 2
    M = 3 ** (J + 2)
    pref = (pow(4, r, M) + (3 ** (v + 1)) * pow(4, r, M) * (c_mod(v, J + 2 - v - 1) % (3 ** (J + 2 - v - 1))) * (u % (3 ** (J + 1 - v)))) % M
    ok = all(digits3(pow(4, K, M) % (3 ** (j + 2)), j) == digits3(pref % (3 ** (j + 2)), j)
             for j in range(v + 1, 2 * v + 2))
    if ok: okw += 1
    else: badw += 1
print(f"  rows v+1..2v+1 of 4^K = rows of prefaced object: {okw} ok, {badw} bad")

print()
print("=" * 70)
print("SECTION 7: TOP-TRIT LAW — row v+1 reads u = K // 3^v")
print("=" * 70)
oktop = badtop = 0
for K in range(9, 20000):
    v = v_of(K)
    if v < 1: continue
    u = K // (3 ** v)
    if u > 2: continue
    if digits3(pow(4, K, 3 ** (v + 3)), v + 1) == u % 3:
        oktop += 1
    else:
        badtop += 1
print(f"  row v+1 of 4^K = u mod 3 (u in {{1,2}}, K in [9,20000)): {oktop} ok, {badtop} bad")
killed = 0; surv = []
for K in range(18, 20000):
    v = v_of(K)
    if v < 1: continue
    if K // (3 ** v) != 2: continue
    clean = all(digits3(pow(4, K, 3 ** (j + 1)), j) != 2 for j in range(1, v + 1))
    if clean:
        fr = fire_row(K, 60)
        if fr == v + 1: killed += 1
        else: surv.append((K, fr, v))
print(f"  top-trit-2 K, rows 1..v clean: die EXACTLY at row v+1: {killed}, exceptions: {len(surv)}")
if surv: print(f"    exceptions: {surv[:10]}")

print()
print("=" * 70)
print("SECTION 8: SURVIVORS — full clean scan below 4000 (16.7M exhaustive = cited receipt)")
print("=" * 70)
survivors = []
for K in range(0, 4000):
    n = 4 ** K
    clean = True
    while n > 0:
        if n % 3 == 2: clean = False; break
        n //= 3
    if clean: survivors.append(K)
print(f"  K in [0,4000) with NO digit 2 anywhere in 4^K: {survivors}")

print()
print("=" * 70)
print("SECTION 9: THE DESCENT/SELF-READ — row j+1 of 4^(1+3m) vs row j of 4^m")
print("=" * 70)
firstdiff = {}
for m in range(1, 3000):
    K = 1 + 3 * m
    for j in range(1, 9):
        a = digits3(pow(4, K, 3 ** (j + 3)), j + 1)
        b = digits3(pow(4, m, 3 ** (j + 2)), j)
        if a != b:
            firstdiff[j] = firstdiff.get(j, 0) + 1; break
    else:
        firstdiff[9] = firstdiff.get(9, 0) + 1
print(f"  first-differing row j histogram (m in [1,3000)): {sorted(firstdiff.items())}")

print()
print("=" * 70)
print("SECTION 10: c_INFTY-PRODUCT READS — the kill position vs c_v * 4^r")
print("=" * 70)
checked = hits = 0
cases = []
for (K, fr, v) in dust_window[:400]:
    if v < 2: continue
    r = K % (3 ** v)
    X = (c_mod(v, PREC) * pow(4, r, 3 ** PREC)) % (3 ** PREC)
    t = (X // (3 ** (fr - v - 1))) % 3
    checked += 1
    if t == 2: hits += 1
    if len(cases) < 10:
        ctx = [(X // (3 ** p)) % 3 for p in range(max(0, fr - v - 4), min(PREC, fr - v + 2))]
        cases.append((K, v, r % 1000, fr, fr - v - 1, ctx))
print(f"  dodgers: trit (fire_row - v - 1) of (c_v * 4^r) == 2: {hits}/{checked}")
for c in cases:
    print(f"    K={c[0]}, v={c[1]}, r%1000={c[2]}, fire_row={c[3]}, pos={c[4]}, ctx={c[5]}")
print()
print("RECEIPT END — all computations exact big-int, bounded loops, modular tower arithmetic.")
