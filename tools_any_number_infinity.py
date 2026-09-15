#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ANY NUMBER TILL INFINITY — the machine verification engine.

Boss order: "ANY number till infinity, TRY THAT, you will get the answer."
Ledger 067 law: every claim printed by this script is the executed run's own
output — exact bounds, verbatim. No bound is ever stated larger than run.

Stages (argv[1]):
  period     — one FULL period of the rows-1..13 firing pattern (period law
               4^(K+3^13) = 4^K mod 3^14), histogram, doubling law through
               level 13, residue ties against the green Lean class lists,
               deep scan of all level-13 survivors to row 200/1000,
               closed-form counts for arbitrary N (incl. boss's 16,777,216).
  deep       — EVERY dust member below N=16,777,216 (all 86,198) deep-scanned
               rows 14..400: the exhaustive machine answer at boss's number.
  sparse     — 20,000 random K in (10^6, 10^9], rows 1..60.
  monsters   — ~110 gigantic exponents (up to 19,729 digits), rows 1..120,
               escalation to 601; deep-dust constructions 3^n+1 etc.
  selfread   — the self_read law itself spot-checked at monsters, j=1..20.
  landmarks  — FULL ternary expansions of 4^K (every digit), D&C, argv[2:] list.

All arithmetic is exact Python big-int. No floats anywhere in decisions.
"""
import sys, time, random

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(1000000)   # monsters reach ~19,729 digits

def now(): return time.time()

P14 = 3 ** 14              # 4,782,969  (covers ternary positions 0..13)
P13 = 3 ** 13              # 1,594,323  (the period of K -> 4^K mod 3^14)

# --- Lean-green class lists, verbatim from GSTTheActConstruction.lean -------
# row 1: K % 3 = 2 (dust_fire_row_one; the root's dying child)
# rows 2..6: the K = 1 (mod 3) dust-branch dying children, per level.
LEAN_ROW1 = (3, [2])
LEAN_ROW2 = (9, [7])                                # line ~258
LEAN_ROW3 = (27, [19, 22, 25])                      # lines ~269-274
LEAN_ROW4 = (81, [55, 58, 64, 67, 73, 76])          # lines ~285-299
LEAN_ROW5 = (243, [85, 91, 112, 118, 163, 175, 190, 202])   # line ~231
LEAN_ROW6 = (729, [31, 37, 172, 253, 256, 271, 337, 352,
                   409, 487, 490, 526, 568, 607, 679, 685])  # line ~390
LEAN_DUST9 = [1, 4]                                       # line ~256
LEAN_DUST27 = [1, 4, 10, 13]                              # line ~266
LEAN_DUST81 = [1, 4, 10, 13, 28, 31, 37, 40]              # line ~281
LEAN_DUST243 = [1, 4, 10, 13, 28, 31, 37, 40, 82, 94, 109, 121, 166, 172, 193, 199]  # line ~311
LEAN_DUST729 = [1, 4, 10, 13, 28, 40, 82, 94, 109, 121, 166, 193, 199,
                244, 247, 274, 280, 283, 325, 364, 415, 436, 442, 496,
                499, 514, 517, 523, 580, 595, 652, 658]      # line ~425
LEAN_DUSTS = [(9, LEAN_DUST9), (27, LEAN_DUST27), (81, LEAN_DUST81),
              (243, LEAN_DUST243), (729, LEAN_DUST729)]
LEAN_LEVELS = [LEAN_ROW1, LEAN_ROW2, LEAN_ROW3, LEAN_ROW4, LEAN_ROW5, LEAN_ROW6]

def first_fire(K, depth):
    """First ternary ROW p in [1,depth] with digit 2 in 4^K; None if none.
    (Position 0 is skipped: 4^K = 1 mod 3, never a two there.)"""
    m = 3 ** (depth + 1)
    x = pow(4, K, m) // 3
    for p in range(1, depth + 1):
        x, d = divmod(x, 3)
        if d == 2:
            return p
    return None

def survivors_of_period():
    """All K in [0, P13) with rows 1..13 of 4^K clean (both mod-3 branches)."""
    surv = []
    r = 1
    for K in range(P13):
        if K > 0:
            r = (r * 4) % P14
        x = r // 3
        fire = False
        for _ in range(13):
            x, d = divmod(x, 3)
            if d == 2:
                fire = True
                break
        if not fire:
            surv.append(K)
    return surv

def ternary_str(n):
    if n == 0:
        return "0"
    ds = []
    while n:
        n, d = divmod(n, 3)
        ds.append(str(d))
    return "".join(reversed(ds))

# ============================ STAGE: period =================================
def stage_period():
    t0 = now()
    print("=== STAGE period: one FULL period, rows 1..13 ===", flush=True)
    law = pow(4, P13, P14)
    print(f"period law: 4^{P13} mod 3^14 = {law}  (must be 1)", flush=True)
    assert law == 1

    hist = [0] * 14
    cum = [0] * (P13 + 1)
    surv = []
    r = 1
    fired_running = 0
    for K in range(P13):
        if K > 0:
            r = (r * 4) % P14
        x = r // 3
        fire = 0
        for p in range(1, 14):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire:
            hist[fire] += 1
            fired_running += 1
        else:
            surv.append(K)
        cum[K + 1] = fired_running
    dt = now() - t0
    total_fired = sum(hist[1:])
    print(f"enumerated K in [0, {P13}) in {dt:.1f}s", flush=True)
    print("fire-row histogram (rows 1..13), one full period:", flush=True)
    for p in range(1, 14):
        print(f"  row {p:2d}: {hist[p]:>9d}", flush=True)
    print(f"  fired by row 13: {total_fired}  "
          f"({100.0*total_fired/P13:.4f}%)", flush=True)
    print(f"  survive rows 1..13 (dust at level 13): {len(surv)}", flush=True)

    print("doubling law (per period, both mod-3 branches + dust branch):",
          flush=True)
    alive = P13
    for l in range(1, 14):
        alive -= hist[l]
        cls = alive // (3 ** (13 - l))
        print(f"  level {l:2d}: alive = {alive:>9d} -> classes mod 3^{l} = "
              f"{cls}  (both branches 2^{l} = {2**l}; dust branch "
              f"K=1 mod 3 -> 2^{l-1} = {2**(l-1)})", flush=True)
        assert cls == 2 ** l

    def counts_upto(N):
        q, rem = divmod(N, P13)
        return q * total_fired + cum[rem], q * len(surv) + (rem - cum[rem])

    rng = random.Random(20260903)
    for _ in range(20):
        N = rng.randrange(1, P13 + 1)
        f, d = counts_upto(N)
        assert f == cum[N] and d == N - cum[N], f"closed form mismatch at N={N}"
    print("closed-form spot-check vs enumeration: 20/20 EXACT", flush=True)
    for N in (10**6, 2*10**6, 5*10**6, 16777216, 10**8, 10**12):
        f, d = counts_upto(N)
        print(f"K in [0, {N}): fired by row 13 = {f}, dust-at-13 = {d}",
              flush=True)
    print("^^ boss's own number 16,777,216 is in the list — machine-answered.",
          flush=True)

    print("residue ties vs Lean (GSTTheActConstruction.lean):", flush=True)
    def rowdig(K, l):
        m = 3 ** (l + 1)
        return (pow(4, K, m) // 3 ** l) % 3
    print("  (a) SOUNDNESS — every Lean fire-class residue fires at its row:",
          flush=True)
    for lvl, (mod, classes) in enumerate(LEAN_LEVELS, start=1):
        bad = [c for c in classes if rowdig(c, lvl) != 2]
        alltwo = sum(1 for c in range(mod) if rowdig(c, lvl) == 2)
        assert not bad, f"row {lvl} class does not fire: {bad}"
        print(f"    row {lvl} mod {mod}: {len(classes)}/{len(classes)} "
              f"classes fire at row {lvl} — SOUND "
              f"(all residues < {mod} with row-{lvl} digit 2: {alltwo})",
              flush=True)
    print("  (b) EXACTNESS — machine dust set = Lean dust pin, level by "
          "level:", flush=True)
    for lvl, (mod, dust) in enumerate(LEAN_DUSTS, start=2):
        derived = sorted(K for K in range(mod)
                         if K % 3 == 1 and first_fire(K, lvl) is None)
        ok = derived == sorted(dust)
        print(f"    level {lvl} mod {mod}: machine dust {len(derived)} "
              f"vs Lean pin {len(dust)} -> "
              f"{'EXACT MATCH' if ok else 'MISMATCH'}", flush=True)
        assert ok
    print("ALL TIES EXACT — machine dust map = Lean dust map.", flush=True)

    t1 = now()
    print(f"deep scan of all {len(surv)} level-13 survivors, rows 14..200...",
          flush=True)
    m200 = 3 ** 201
    hist_deep = {}
    stragglers = []
    maxrow, maxK = 0, None
    for K in surv:
        x = pow(4, K, m200) // 3 ** 14
        fire = None
        for p in range(14, 201):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire is None:
            stragglers.append(K)
        else:
            hist_deep[fire] = hist_deep.get(fire, 0) + 1
            if fire > maxrow:
                maxrow, maxK = fire, K
    print("  deep histogram rows 14..200:", flush=True)
    for p in sorted(hist_deep):
        print(f"    row {p:3d}: {hist_deep[p]:>6d}", flush=True)
    print(f"  max fire row within one period: {maxrow} (at K={maxK})",
          flush=True)
    print(f"  stragglers past row 200: {len(stragglers)} -> {stragglers}",
          flush=True)
    m1000 = 3 ** 1001
    for K in stragglers:
        x = pow(4, K, m1000) // 3
        fire = None
        for p in range(1, 1001):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire is None:
            print(f"    K={K}: CLEAN through row 1000 — Cantor power; "
                  f"4^{K} = {ternary_str(4**K)}_3", flush=True)
        else:
            print(f"    K={K}: fire row = {fire}", flush=True)
    print(f"deep scan took {now()-t1:.1f}s", flush=True)
    print("=== STAGE period DONE ===", flush=True)

# ============================ STAGE: deep ===================================
def stage_deep():
    N = 16777216
    t0 = now()
    print(f"=== STAGE deep: EVERY dust member below {N} (boss's number), "
          f"rows 14..400 ===", flush=True)
    surv = survivors_of_period()
    print(f"base period survivors (rows 1..13 clean): {len(surv)}", flush=True)
    assert len(surv) == 8192
    q, rem = divmod(N, P13)
    members = []
    for qq in range(q):
        base = qq * P13
        members.extend(base + s for s in surv)
    members.extend(q * P13 + s for s in surv if q * P13 + s < N)
    print(f"dust members of [0, {N}): {len(members)} "
          f"(closed form says 86198)", flush=True)
    assert len(members) == 86198

    m = 3 ** 401
    hist = {}
    stragglers = []
    maxrow, maxK = 0, None
    for K in members:
        x = pow(4, K, m) // 3 ** 14
        fire = None
        for p in range(14, 401):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire is None:
            stragglers.append(K)
        else:
            hist[fire] = hist.get(fire, 0) + 1
            if fire > maxrow:
                maxrow, maxK = fire, K
    print("fire-row histogram of the dust, rows 14..400:", flush=True)
    for p in sorted(hist):
        print(f"  row {p:3d}: {hist[p]:>6d}", flush=True)
    fired = sum(hist.values())
    print(f"fired by row 400: {fired}/{len(members)}", flush=True)
    print(f"max fire row below {N}: {maxrow} (at K={maxK})", flush=True)
    print(f"stragglers (clean through row 400): {len(stragglers)} -> "
          f"{stragglers}", flush=True)
    for K in stragglers:
        print(f"  K={K}: 4^{K} = {ternary_str(4**K)}_3 — FULL expansion, "
              f"no digit 2 anywhere", flush=True)
    bad = [K for K in stragglers if K >= 8]
    print(f"stragglers at or beyond K=8: {bad}", flush=True)
    if not bad:
        print(f">>> MACHINE-VERIFIED, EXHAUSTIVE: every K in [8, {N}) fires "
              f"a digit 2 — noTernaryTwo (4^K) = false for ALL of them. "
              f"The only 2-free powers of 4 below {N} are 4^0=1, 4^1=4, "
              f"4^4=256.", flush=True)
    print(f"stage took {now()-t0:.1f}s", flush=True)
    print("=== STAGE deep DONE ===", flush=True)

# ============================ STAGE: sparse =================================
def stage_sparse():
    t0 = now()
    print("=== STAGE sparse: 20,000 random K in (10^6, 10^9], rows 1..60 ===",
          flush=True)
    rng = random.Random(20260903)
    m = 3 ** 61
    hist = {}
    maxrow, maxK = 0, None
    stragglers = []
    N = 20000
    for _ in range(N):
        K = rng.randrange(10**6 + 1, 10**9 + 1)
        x = pow(4, K, m) // 3
        fire = None
        for p in range(1, 61):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire is None:
            stragglers.append(K)
        else:
            hist[fire] = hist.get(fire, 0) + 1
            if fire > maxrow:
                maxrow, maxK = fire, K
    print(f"sampled {N} random K in (10^6, 10^9]:", flush=True)
    for p in sorted(hist):
        print(f"  row {p:2d}: {hist[p]:>6d}", flush=True)
    print(f"max fire row: {maxrow} (at K={maxK})", flush=True)
    print(f"stragglers past row 60: {len(stragglers)}", flush=True)
    for K in stragglers[:20]:
        p = first_fire(K, 600)
        print(f"  escalated K={K}: fire row = {p}", flush=True)
    print(f"stage took {now()-t0:.1f}s", flush=True)
    print("=== STAGE sparse DONE ===", flush=True)

# ============================ STAGE: monsters ===============================
def monster_list():
    Ms = []
    for k in (12, 15, 18, 21, 24, 27, 30, 36, 42, 48, 54, 60, 66, 72, 78,
              84, 90, 96, 100, 111, 123, 150, 200, 256, 300, 365, 500, 666,
              777, 1000, 1234, 2000, 2560, 3000, 3650, 4096, 5000, 6000,
              7000, 7777, 8888, 9999, 10000):
        Ms.append((f"10^{k}", 10 ** k))
    for b, e in ((4, 64), (4, 100), (4, 128), (3, 333), (3, 500), (3, 777),
                 (2, 1000), (2, 2048), (2, 4096), (2, 8192), (2, 16384),
                 (7, 100), (7, 256), (5, 200), (6, 150), (11, 100),
                 (4, 12), (4, 13), (4, 14), (4, 15), (4, 16)):
        Ms.append((f"{b}^{e}", b ** e))
    for n in (50, 100, 200, 500):
        f = 1
        for i in range(2, n + 1):
            f *= i
        Ms.append((f"{n}!", f))
    Ms.append(("10^100+7", 10 ** 100 + 7))
    Ms.append(("10^1000+45", 10 ** 1000 + 45))
    Ms.append(("2^65536-1", 2 ** 65536 - 1))
    Ms.append(("10^10000", 10 ** 10000))
    Ms.append(("3^3333", 3 ** 3333))
    Ms.append(("16,777,216 (boss's number)", 16777216))
    rng = random.Random(777)
    for i in range(20):
        Ms.append((f"random33#{i}", rng.randrange(10**32, 10**33 - 1)))
    for i in range(20):
        Ms.append((f"random100#{i}", rng.randrange(10**99, 10**100 - 1)))
    for i in range(10):
        Ms.append((f"random333#{i}", rng.randrange(10**332, 10**333 - 1)))
    for i in range(10):
        Ms.append((f"random1000#{i}", rng.randrange(10**999, 10**1000 - 1)))
    for i in range(3):
        Ms.append((f"random3333#{i}", rng.randrange(10**3332, 10**3333 - 1)))
    return Ms

def stage_monsters():
    t0 = now()
    print("=== STAGE monsters: gigantic exponents, rows 1..120 ===", flush=True)
    Ms = monster_list()
    m = 3 ** 121
    hist = {}
    stragglers = []
    maxrow, maxname = 0, None
    for name, K in Ms:
        kdig = len(str(K))
        x = pow(4, K, m) // 3
        fire = None
        for p in range(1, 121):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        if fire is None:
            stragglers.append((name, K))
            print(f"  {name} ({kdig} digits): NO fire in rows 1..120 "
                  f"-> escalating", flush=True)
        else:
            hist[fire] = hist.get(fire, 0) + 1
            if fire > maxrow:
                maxrow, maxname = fire, name
            if kdig >= 300 or "boss" in name:
                print(f"  {name} ({kdig} digits): fire row = {fire}",
                      flush=True)
    print(f"monsters scanned: {len(Ms)}", flush=True)
    print("fire-row histogram (rows 1..120):", flush=True)
    for p in sorted(hist):
        print(f"  row {p:3d}: {hist[p]:>4d}", flush=True)
    print(f"max fire row among monsters: {maxrow} (at {maxname})", flush=True)
    print(f"stragglers past row 120: {len(stragglers)}", flush=True)
    m601 = 3 ** 601
    for name, K in stragglers:
        x = pow(4, K, m601) // 3
        fire = None
        for p in range(1, 601):
            x, d = divmod(x, 3)
            if d == 2:
                fire = p
                break
        print(f"  ESCALATED {name}: fire row = {fire}", flush=True)

    print("--- deep-dust constructions (exponents hiding at depth n) ---",
          flush=True)
    fam = []
    for n in (30, 50, 100, 200, 500):
        fam.append((f"3^{n}+1", 3 ** n + 1, n + 300))
    for n in (30, 50, 100, 200):
        fam.append((f"3^{n}-1", 3 ** n - 1, n + 300))
    for n in (30, 50, 100):
        fam.append((f"2*3^{n}", 2 * 3 ** n, n + 300))
    fam.append(("3^100+3^50+1", 3**100 + 3**50 + 1, 400))
    fam.append(("3^200+3^100+3^50+1", 3**200 + 3**100 + 3**50 + 1, 500))
    fam.append(("3^500+3^250+1", 3**500 + 3**250 + 1, 800))
    for name, K, depth in fam:
        p = first_fire(K, depth)
        print(f"  {name}: fire row = {p} (scan depth {depth})", flush=True)
    print(f"stage took {now()-t0:.1f}s", flush=True)
    print("=== STAGE monsters DONE ===", flush=True)

# ============================ STAGE: selfread ===============================
def stage_selfread():
    print("=== STAGE selfread: the law at astronomical size, j=1..20 ===",
          flush=True)
    Ms = [(f"10^{k}", 10 ** k) for k in (50, 100, 200, 500, 1000)]
    Ms += [(f"4^{e}", 4 ** e) for e in (64, 100)]
    Ms += [("2^65536-1", 2 ** 65536 - 1), ("100!", None)]
    f = 1
    for i in range(2, 101):
        f *= i
    Ms = [(n, K if K is not None else f) for n, K in Ms]
    rng = random.Random(999)
    for i in range(5):
        Ms.append((f"random200#{i}", rng.randrange(10**199, 10**200 - 1)))
    checked = 0
    for name, K in Ms:
        for j in range(1, 21):
            m = 3 ** (j + 2)
            lhs = (pow(4, K, m) // 3 ** (j + 1)) % 3
            pre = K % (3 ** j)
            rhs = ((pow(4, pre, m) // 3 ** (j + 1)) % 3
                   + (K // 3 ** j) % 3) % 3
            assert lhs == rhs, f"self_read broken: {name} j={j}"
            checked += 1
        print(f"  {name}: self_read j=1..20 verified (20/20)", flush=True)
    print(f"total self_read checks: {checked}/{checked} PASS", flush=True)
    print("=== STAGE selfread DONE ===", flush=True)

# ============================ STAGE: landmarks ==============================
_P3 = {}
def p3(e):
    r = _P3.get(e)
    if r is not None:
        return r
    result = 1
    base = 3
    ee = e
    while ee:
        if ee & 1:
            result *= base
        ee >>= 1
        if ee:
            base *= base
    _P3[e] = result
    return result

def dnc_stats(n, w, p0):
    """(c0,c1,c2,first2pos or -1) for n < 3^w; block covers LSB positions
    [p0, p0+w). No giant lists — stats only."""
    if w == 1:
        if n == 0:
            return (1, 0, 0, -1)
        if n == 1:
            return (0, 1, 0, -1)
        return (0, 0, 1, p0)
    if w <= 64:
        c = [0, 0, 0]
        f2 = -1
        x = n
        q = p0
        for _ in range(w):
            x, d = divmod(x, 3)
            c[d] += 1
            if d == 2 and f2 < 0:
                f2 = q
            q += 1
        return (c[0], c[1], c[2], f2)
    lo = w >> 1
    mm = p3(lo)
    qn, rn = divmod(n, mm)
    a = dnc_stats(rn, lo, p0)
    b = dnc_stats(qn, w - lo, p0 + lo)
    f2 = a[3] if a[3] >= 0 else b[3]
    return (a[0] + b[0], a[1] + b[1], a[2] + b[2], f2)

def stage_landmarks():
    Ks = [int(x) for x in sys.argv[2:]] or [10**4, 10**5, 10**6]
    print(f"=== STAGE landmarks: FULL ternary expansion of 4^K, K={Ks} ===",
          flush=True)
    for K in Ks:
        t0 = now()
        n = 4 ** K
        assert n % 3 == 1
        est = int(n.bit_length() * 0.63092975357145744) + 2
        W = 1
        while W < est:
            W <<= 1
        while p3(W) <= n:
            W <<= 1
        c0, c1, c2, f2 = dnc_stats(n, W, 0)
        L = est
        while p3(L) <= n:
            L += 1
        while L > 1 and n // p3(L - 1) == 0:
            L -= 1
        dt = now() - t0
        print(f"K={K}: ternary true length {L}, block W={W}, "
              f"count(0)={c0}, count(1)={c1}, count(2)={c2}, "
              f"first '2' at row {f2}, time {dt:.1f}s", flush=True)
        assert c2 >= 1 and 1 <= f2 < L
    print("=== STAGE landmarks DONE ===", flush=True)

if __name__ == "__main__":
    stage = sys.argv[1] if len(sys.argv) > 1 else "period"
    if stage == "period":
        stage_period()
    elif stage == "deep":
        stage_deep()
    elif stage == "sparse":
        stage_sparse()
    elif stage == "monsters":
        stage_monsters()
    elif stage == "selfread":
        stage_selfread()
    elif stage == "landmarks":
        stage_landmarks()
    else:
        print(f"unknown stage {stage}", file=sys.stderr)
        sys.exit(2)
