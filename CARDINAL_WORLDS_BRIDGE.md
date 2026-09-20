# THE CARDINAL WORLDS BRIDGE — CI-GREEN RECEIPTS

Branch: `astra/cardinal-worlds-bridge` @ `8139d6308c75c2b267ece6d4d1c4a17c12fc7414`
CI run: `35521907253` (Lean Action CI) — **SUCCESS**
Hard build: SUCCESS · Exact V5 comparator: SUCCESS (`Your solution is okay! /
Status: CLEAN ✓ / COMPARATOR RESULT: PASS`) · Kernel axiom audit: SUCCESS.

## THE MODULE

`GSTCardinalWorldsBridge.lean` (≈ 800 lines) — the 2-world × 3-world × GST
combination, per the directive: **Postulate I and the other bridges, NOT
Postulate II**.

## THE THEOREMS (all `[propext, Classical.choice, Quot.sound]`, zero sorryAx)

### §1 THE ×2 BRIDGE — the signature injection law (`C ∩ 2C = {0}`)
- `two_mul_cantor_kill` — **THE ×2 BRIDGE LAW**: a number and its double
  are both Cantor-clean in the first `k` trits only if the number is zero
  in that window. Doubling a clean ternary word doubles each trit
  digitwise (no carries: `0,1 ↦ 0,2`), so a live trit `1` becomes the
  bridge signature `2`. The 2-world generator cannot act on a nonzero
  Cantor object without injecting the signature.
- `two_mul_cantor_kill_all` — the all-depths form: a nonzero all-depths
  Cantor object has a dirty double.

### §2 THE d-TOWER LAWS — Postulate I machinery
- `d_recurrence` — **THE d-TOWER SQUARE-LIFT RECURRENCE**
  `d(j+1) = d(j) + 2^(j+1)·d(j)²` — the 2-world dual of the c-tower's
  cube lift, verbatim from `2^(j+2)·d(j) = 3^(2^j) − 1` by squaring.
- `d_mod3_parity` — `d(j) ≡ 2 (mod 3)` for even `j`, `≡ 1` for odd.
- `d_mod9_cycle` — **THE MOD-9 SIX-CYCLE**: for `j ≥ 3`,
  `j mod 6 = 0,1,2,3,4,5 ↦ d(j) mod 9 = 2,1,5,7,8,4`. The cycle
  `2 → 1 → 5 → 7 → 8 → 4 → 2` is closed by the square-lift recurrence
  driven by the 2-world period `2^j mod 9` (period 6). Postulate I's
  face: the signature fires at trit zero for `j ≡ 0,2,4 (mod 6)`, at
  trit one for `j ≡ 3`; the classes `j ≡ 1,5 (mod 6)` (values `1,4`
  mod 9 — clean at trits zero and one) are the DEEP classes — the exact
  mirror of the Erdős clean tree (`b ≡ 1,4 (mod 9)` for the powers).
- `postulate_I_fire_outside_deep` — for every `j ≥ 2` outside the deep
  classes, the bridge signature fires (cites the monolith's green
  `bridge_sig_even` / `bridge_sig_j_mod6_3`).

### §3 THE SKEWED MIRROR
- `cardinal_worlds_mirror` — the c-tower (3-world, cube lift
  `+3^(s+1)·c² + 3^(2s+1)·c³`) and the d-tower (2-world, square lift
  `+2^(j+1)·d²`) are dual cascades across the bridge `3 = 1 + 2`. The
  skew (`2·3^s` vs `2^j`, `s+1` vs `j+2`) IS the bridge signature.

### §4 THE FIRE TRANSPORT
- `cut_shift_general` — **THE CUT-WORD DIGIT SHIFT**: if
  `4^E = 1 + 3^(s+1)·W`, the power's trit at row `s+1+i` IS the cut
  word's trit at row `i`. A fire in the shadow is a fire in the power.
- `cut_shift_s0` — the sheet-zero instance.

### §5 THE SHEET DECOMPOSITION
- `sheet_decompose` — every `K ≥ 1` is `3^s·core` with `3 ∤ core`.

### §6 THE PROMOTION — hTailF AS A THEOREM FROM TWO TRANSPARENT SLICES
- `s0_premise_full_clean` — **THE s = 0 CIRCULARITY RECEIPT**: the s = 0
  content of the `omegaShadowTailF` premise (the all-depths row observer
  clause) forces `4^core` to be Cantor-clean at EVERY position — the
  premise IS the negation of the conclusion. The s = 0 family of the
  tailF can only be satisfied vacuously.
- `four_power_omega_shadow_wave_tailF_of_slices` — **THE PROMOTION**:
  `hTailF` is a THEOREM under
  - `hWave` — the Ω-shadow wave over all sheets `s ≥ 1`: every 3-free
    core `≥ 2` fires in its cut word;
  - `hS0` — the sheet-zero slice: every 3-free `a ≥ 5` in the deep
    classes `a ≡ 1,4 (mod 9)` fires.
  The s = 0 premise is REFUTED by `hS0` (circularity receipt); the
  s ≥ 1 premise is transported by the digit shift.

### §7 THE CROWN
- `erdos_even_of_slices` — under the two slices, every `4^K` (`K ≥ 8`)
  owns its ternary digit two. Coverage: sheets `s ≥ 1` by `hWave`
  (digit shift; the unit-tail `core = 1` by the `lteCoeff ≡ 7 (mod 9)`
  window); sheet zero by the green mod-9/mod-27 windows (`K ≡ 2 (mod 3)`
  fires at row 1, `K ≡ 7 (mod 9)` at row 2) and `hS0` for the deep
  classes.
- `erdos_even_conjecture_of_slices` — the `noTernaryTwo` form.

## THE REDUCTION MAP (what the two slices are)

The dissection of this module + the prior campaign forensics:
- `hWave` = the Ω-shadow wave over the deep sheets = the seam's s-family
  (the clean-tree descent; every prior route lands on it).
- `hS0` = the sheet-zero residual in the two deep classes — the
  bounded-computational slice (green to `2·10^6` by the monolith's
  `modular_depth_s0`).
- The d-tower's deep classes (`j ≡ 1,5 (mod 6)`) are the exact 2-world
  mirror of the Erdős deep classes (`b ≡ 1,4 (mod 9)`): the cardinal
  worlds' skew-duality, now formalized (`cardinal_worlds_mirror` +
  `d_mod9_cycle`).

## CI ITERATION LEDGER (5 runs)

- run 1 (`35512108866`): 53 mechanical errors (rw directions, mod_lt
  moduli, dvd witness, defeq-vs-syntactic, ih double-application,
  omega-disjunction misuse).
- run 2 (`35514823678`): 29 errors (omega cannot relate pow/div
  monomials; all-W rewrites hitting RHS occurrences; auto-closed rw
  chains).
- run 3 (`35517139332`): 22 errors (component-order bug in the 6-lambda
  refinements; mod-context pollution of omega; h2a comm; j=0 logic bug).
- run 4 (`35519564495`): 9 errors (the position-2/hW1v routing; six
  auto-closed decides; h5 assoc).
- run 5 (`35521907253`): **SUCCESS** — full green.
