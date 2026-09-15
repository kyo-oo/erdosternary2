# DERIVATION E — THE DUST EMPTY (the heart): the tower-factorization, the deformed-Cantor automaton, and the two-phase kill

Lane E (the heart lane — orchestrator-executed after the four-agent parallel volley
died at the tool's context ceiling; one-response-or-done). Machine receipts:
`HEART_ATTACK_RECEIPTS.txt` + `DEAD_CHILD_RECEIPTS.txt` (this session, exact big-int,
bounded loops, modular tower arithmetic) and the T1–T4 receipts quoted in
`GSTTowerFire.lean`'s docstring. Zero Lean bytes in this file.

---

## §0 THE TARGET, RESTATED THREE WAYS

GAP-A2 (sheet-zero dust emptiness — the heart): every three-free natural K ≥ 8 fires,
i.e. ∃ j ≥ 1 with digit3 (4^K) j = 2. Green context: `the_act_iff_no_cantorian`
(the act ⟺ no Cantorian exponent from 8 on), `cantorian_survivors_below_eight`
= exactly {0,1,4}; three-free K ≡ 2 mod 3 dies at row 1 (front law), so the residual
is K = 1 + 3m with m ≥ 3 (K ≥ 10); K ∈ {1,4} are the true survivors.

**Form 1 (automaton).** Define the dust tree: nodes at level L are residues
r mod 3^L whose rows 1..L of 4^r are clean (row j of 4^K depends only on
K mod 3^j — GREEN `wave_digit_periodic` at a=0). Each node has exactly one dead
child (GREEN `unique_dead_child`): the child r + t·3^L whose row L+1 reads 2.
Write d(node, L) ∈ {0,1,2} for the dead child's trit. Then:

> GAP-A2 ⟺ for every m ≥ 3 with eventually-zero trits, walking the tree by m's
> actual trits, some level L has trit_L(m) = d(m's node, L).

**Form 2 (constant path).** A natural m has support D = ⌊log₃ m⌋; beyond it the
trits are 0, so the node sequence is eventually CONSTANT at m itself. GAP-A2 ⟺
along every constant path from a dust node m ≥ 3, the dead label d eventually
equals 0 (the zero-child dies) — or a within-support collision occurs first.

**Form 3 (multiplicative — NEW, this lane).** See §1.

---

## §1 THE MULTIPLICATIVE TOWER-FACTORIZATION (NEW; receipt 200/200)

**Identity (E1).** 4^K = Π_t (1 + 3^(t+1)·c_t)^(trit_t(K)), where
c_t = (4^(3^t) − 1)/3^(t+1) — each factor IS exactly 4^(3^t).

*Proof.* 4^K = Π_t (4^(3^t))^(trit_t K) = Π_t (1+3^(t+1)c_t)^(trit_t K) by the
green tower decomposition (now GREEN in Lean: `GSTTowerFire.four_pow_three_pow_eq`). ∎

*Receipt.* 200/200 random K ∈ [0, 3000), exact big-int product vs 4^K (§2 of
HEART_ATTACK_RECEIPTS).

**The conjecture in multiplicative form.** No-2-trit values of
Π_t (1+3^(t+1)c_t)^(trit_t) occur only at K ∈ {0, 1, 4}: the empty product (=1),
the single t=0 factor (=4), and the t=0,t=1 product (=256 = 100111₃). Everything
else — every other finite multiset of tower factors — contains a 2-trit.

**Why this matters.** The c_t are universal and stabilize: c_{t+1} ≡ c_t
mod 3^(t+1) (receipt 26/26; GREEN in Lean via `c_succ_eq`), so c_t's first t+1
trits are c_∞'s. The corrections inside every deep read are governed by ONE
constant, c_∞, whose trit stream (receipt, recomputed to 24 positions — extends
Lane D's 12):

    c_∞ = [1, 2, 1, 0, 2, 2, 0, 1, 0, 2, 1, 2, 1, 0, 1, 1, 2, 1, 0, 0, 0, 1, 2, 0, ...]
    2-positions: {1, 4, 5, 9, 11, 16, 22, ...}

The blade = the trit-carries of these products; the deep rows read polynomial
forms in K's trits with c_∞-driven coefficients.

---

## §2 THE DEFORMED-CANTOR AUTOMATON (NEW; tables L = 1..7)

Pure Cantor would mean d(node, L) = 2 at every node (the trit-2 child always dies).
The machine says: **the dust tree is a DEFORMATION of the Cantor tree, and the
deformation begins exactly at level 5.** Full dead-label tables (DEAD_CHILD_RECEIPTS):

* L=1..3: pure Cantor. All 1+2+4 nodes have d = 2. (Consistent with the GREEN
  dust-root laws: rows 2,3,4 read m's trits 0,1,2 bare — the blade's first
  correction C(m,2) vanishes on the Cantor path because C(m,2) ≡ [m ≡ 2 mod 3].)
* L=4 (row 5): **the flip.** d = 1 on nodes {4, 10, 31, 37} (m ≡ 1, 3 mod 9),
  d = 2 on the rest. The trit-1 child dies; the trit-2 child LIVES — the
  blade's first active correction, and the machine's famous four
  {166, 172, 193, 199} (the construction's docstring survivors) are exactly
  the trit-2 children that the flip saves.
* L=5 (row 6): **the first natural-killers.** d = 0 on {31, 37, 172}
  (m ∈ {10, 12, 57}), d = 1 on {10, 13, 28, 94, 109, 166}, d = 2 on the rest.
* L=6 (row 7): d = 0 on 10 nodes — **m = 3 and m = 9 among them**
  (nodes 10 and 28): K = 10 = 3²+1 and K = 28 = 3³+1 — Lane D's n+4 law,
  now GREEN in Lean (`three_pow_plus_one_fires`), IS the automaton's d=0 event
  on the powers-of-3 m-path. Full d=0 list: m ∈ {3, 9, 66, 91, 138, 147,
  166, 172, 217, 219}.
* L=7 (row 8): d = 0 on 12 nodes — m = 27 among them (node 82: K = 82 =
  3⁴+1, the n+4 law again). The d=0 population: 3, 6, 10, 12 per level
  (L=5..7) out of 2^(L−1) nodes.

**The period law (corrected).** Row j+2 of 4^(1+3m) depends only on m mod 3^(j+1)
— B_5 has period **81**, not 243 (today's receipt: smaller period 81; the earlier
243 claim was true but not minimal). The "trit_3(m) + corr(m mod 81)" decomposition
FAILS (corr not well-defined — receipt) — consistent with the no-small-closed-form
receipt for B_5..B_8. The blade is genuinely tabular beyond order 4.

**The two-phase kill geometry (K ∈ [8, 100000], all fire, max row 28 at K = 79570):**

* within support + 1: 19322/19992 die (the automaton's shallow phase);
* just above (≤ 2S+2): 642 die (the window phase);
* deep (> 2S+2): 28 die — (10,7), (12,10), (13,10), (36,11), (40,9), (63,10),
  (93,13), (166,15), (237,12), (432,14), (496,13), (567,21), ...

The deep phase is where the c_∞-driven semigroup structure (§3) takes over.

---

## §3 THE DEEP PHASE — support semigroups and the c_∞ stream

For m with support S ⊆ {0..D} (positions of nonzero trits), the multiplicative
form (E1) gives 4^(1+3m) = 4·Π_{t∈S}(1+3^(t+1)c_t)^(trit_t). The deep rows
(beyond K's own trit window) read the trit-carries of these products:

* single-support families are GREEN (`GSTTowerFire`): S = {n} with trit 1
  → the n+2 law (3^n at row n+2); trit 2 → the n+1 law (2·3^n at row n+1);
  the prefixed singleton 3^n + 1 → the n+4 law.
* the general deep read: row n+1+k of 4^(j·3^n) = digit k of j·c_n
  (GREEN: `tower_digit_read` — Lane D's L10, the deep-hider master lemma).
  For multi-support m, the same machinery applies at every cut — the prefaced
  window law (GREEN `prefaced_window_law`) glues the reads level by level.

**The central kill question (sharpest known form).** Along the constant path
of a natural m ≥ 3 (rows beyond the support read the frozen m through blade
tables of growing period, i.e. the deep body of 4^(1+3m) — ~1.26·(1+3m) rows
of room), the reads are the trits of 4·Π_{t∈S}(1+3^(t+1)c_t)^(trit_t) — and the
carry structure at each depth mixes: m's support-sum decompositions with c_∞'s
trit stream (2-positions {1,4,5,9,11,16,22,...}).

**Partial alignment receipt.** Among the 63 window-dodgers of [8, 100000], the
kill position satisfies "trit (fire_row − v − 1) of c_v·4^r = 2" in only 19/63
cases — the naive c_∞-product alignment is NOT the universal kill. The correct
mechanism must combine the support-sum carries with the c_∞ stream (the
two-term-binomial remainder R in `one_add_pow_two_term` carries the deeper
binomial orders — the accumulating blade).

---

## §4 WHAT IS NOW GREEN (this lane's Lean landing: GSTTowerFire.lean)

1. `four_pow_three_pow_eq` — the exact tower decomposition (LTE as equation).
2. `c_succ_eq` — the cube recursion (c_{n+1} = c_n + two binomial corrections).
3. `c_mod3`, `c_mod9`, `c_mod81` — the tower congruences (1; 7 for n ≥ 1; 16 for n ≥ 3).
4. `div_add_lt`, `prefaced_digit`, `one_add_pow_two_term` — the read glue.
5. `tower_digit_read` — **the deep-hider master lemma (L10)**: rows n+1..2n+1 of
   4^(j·3^n) are digits 0..n of j·c_n. ONE constant governs every depth.
6. `three_pow_fires` (L7: 3^n at row n+2), `two_mul_three_pow_fires` (L8: 2·3^n at
   row n+1), `three_pow_plus_one_fires` (L9: 3^n+1 at row n+4 for n ≥ 3).

All receipts in the module docstring (T1 30/30, T2 28/28, T3 31/31, T4 720/720).

---

## §5 THE REMAINING GAP — named exactly

**GAP-A2 (automaton form).** For every eventually-zero trit path m ≥ 3 on the dust
tree: ∃ L with trit_L(m) = d(node at level L). Equivalently (constant-path form):
every dust node m ≥ 3 eventually meets a level where its zero-child dies —
i.e. some deep row of 4^(1+3m) reads 2.

**What is proved vs what remains.** The canonical single-support families are
green (§4). The d=0 population at each level is 3–12 nodes and includes the
powers-of-3 m-path (n+4 law). What remains is the multi-support kill: the
carry interaction between two or more tower factors, governed by c_∞'s stream,
must be shown to plant a 2 in the deep body of every 4^(1+3m), m ≥ 3. The
two-term master lemma is green; the three-term interaction
(the C(j,2)-order read with j's trits) is the named next increment:

> **GAP-E1 (the pair-read lemma).** For all j, n and supports t₁ ≠ t₂ with
> t₁, t₂ ≤ n: the rows n+1..2n+1 of 4^((3^t₁ + 3^t₂)·3^n-multiples) read
> (3^t₁+3^t₂-shifted) c_n-products whose carry term is the pairwise binomial
> C-trit — prove the read formula, then the 2-placement.

**GAP-A1 (conjugation note).** By Lane C's L6 (the deep wave is the blade
conjugated via c_∞) and the green periodicity, the s ≥ 1 window-dodger arm is
the same automaton in wave coordinates: the shadow families (core ≡ 4 mod 9
any s; s ≥ 1 core ≡ 7 mod 9) are the wave-coordinate dust. GAP-E1's pair-read
mechanism, conjugated, is the deep-wave theorem's engine.

---

## §6 RECEIPTS INDEX (all this session, exact big-int, bounded)

* `tools_heart_attack.py` → `HEART_ATTACK_RECEIPTS.txt`: c-tower stabilization
  26/26; c_∞ 24 trits + 2-positions; tower factorization 200/200; B_5 period 81
  (+ no-fit of trit+corr decomposition); dust vs pure-Cantor deviation maps
  L = 1..8; kill-row geometry (max row 28 @ K=79570, 63 dodgers); prefaced
  window law 2991/2991; survivors below 4000 = {0,1,4}; descent first-diff
  histogram; c_∞-product alignment 19/63.
* `tools_dead_child.py` → `DEAD_CHILD_RECEIPTS.txt`: dead-label tables L = 1..7
  (the flip at L=4; d=0 events from L=5; m = 3, 9, 27 among them); dust tf
  classes at L=6 = the green 32-residue pin, exact match.
* T1–T4 numerics (quoted in GSTTowerFire.lean docstring): 30/30, 28/28, 31/31,
  720/720; c 1 % 9 = 7, c 3 % 81 = 16, c 0 = 1.

## §7 SELF-AUDIT (ledger discipline)

* No hedge words; every law carries a receipt count or a green citation.
* Honest negatives recorded: B_5 period 243 → corrected to 81 (minimal);
  trit+corr decomposition refuted; top-trit law (row v+1 = u mod 3) refuted
  (6773/19991); c_∞-product exact-position alignment refuted as the universal
  kill (19/63). All four replaced by the exact green/data statements.
* No unbounded compute: all loops ≤ 10^7, modular tower arithmetic only
  (the v1 script's full-int 4^(3^26) was caught and replaced by modular c_mod
  BEFORE any long run — the no-OOM law held).
* Zero Lean bytes in this file; the Lean landing is GSTTowerFire.lean only.
