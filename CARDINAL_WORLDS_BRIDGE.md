# THE CARDINAL WORLDS BRIDGE — CI-GREEN RECEIPTS

Branch: `astra/cardinal-worlds-bridge` @ `aa3630d9261bab47be731aaa957fd6edd9c596ef`
CI run: `35542150111` (Lean Action CI) — **SUCCESS**
Hard build: SUCCESS · Exact V5 comparator: SUCCESS (`Your solution is okay! /
=== COMPARATOR RESULT: PASS ===`) · Kernel axiom audit: SUCCESS.

## THE MODULE

`GSTCardinalWorldsBridge.lean` — the 2-world × 3-world × GST combination,
per the directive: **Postulate I and the other bridges, NOT Postulate II**.

## THE THEOREMS (all `[propext, Classical.choice, Quot.sound]`, zero sorryAx)

### §1 THE ×2 BRIDGE — the signature injection law (`C ∩ 2C = {0}`)
- `two_mul_cantor_kill` — **THE ×2 BRIDGE LAW**: a number and its double
  are both Cantor-clean in the first `k` trits only if the number is zero
  in that window. Doubling a clean ternary word doubles each trit
  digitwise (no carries: `0,1 ↦ 0,2`), so a live trit `1` becomes the
  bridge signature `2`. The 2-world generator cannot act on a nonzero
  Cantor object without injecting the signature.
- `two_mul_cantor_kill_all` — the all-depths form.

### §2 THE d-TOWER LAWS — Postulate I machinery
- `d_recurrence` — **THE d-TOWER SQUARE-LIFT RECURRENCE**
  `d(j+1) = d(j) + 2^(j+1)·d(j)²`.
- `d_mod3_parity` — `d(j) ≡ 2 (mod 3)` for even `j`, `≡ 1` for odd.
- `d_mod9_cycle` — **THE MOD-9 SIX-CYCLE** `2 → 1 → 5 → 7 → 8 → 4 → 2`;
  the deep classes `j ≡ 1,5 (mod 6)` (values `1,4` mod 9) are the exact
  2-world mirror of the Erdős clean tree.
- `postulate_I_fire_outside_deep` — the bridge signature fires for every
  `j ≥ 2` outside the deep classes (cites the monolith's green
  `bridge_sig_even` / `bridge_sig_j_mod6_3`).

### §3 THE SKEWED MIRROR
- `cardinal_worlds_mirror` — the c-tower (3-world, cube lift) and the
  d-tower (2-world, square lift) are dual cascades across `3 = 1 + 2`.

### §4 THE FIRE TRANSPORT
- `cut_shift_general` — **THE CUT-WORD DIGIT SHIFT**: a fire in the
  shadow is a fire in the power.
- `cut_shift_s0` — the sheet-zero instance.

### §5 THE SHEET DECOMPOSITION
- `sheet_decompose` — every `K ≥ 1` is `3^s·core` with `3 ∤ core`.

### §6 THE PROMOTION FROM THE TWO TRANSPARENT SLICES
- `s0_premise_full_clean` — **THE s = 0 CIRCULARITY RECEIPT**.
- `four_power_omega_shadow_wave_tailF_of_slices` — the promotion under
  `hWave` + `hS0`.

### §7 THE CROWN
- `erdos_even_of_slices` / `erdos_even_conjecture_of_slices`.

### §8 THE CARDINAL WORLDS LAW-PROMOTION — hTailF AS A THEOREM OF THE
GRANTED LAWS (this is the terminal form)
- `lteCoeff_has_two` — **THE 3-WORLD TOWER-TWIN RECEIPT**: the c-tower
  (LTE mean cascade) fires at every sheet from one on (`lteCoeff s ≡ 7
  (mod 9)`, the word `21`). The 3-world's twin of Postulate I's proven
  faces. Axioms: `[propext, Quot.sound]`.
- `four_pow_mul_d` — **THE 6-WORLD PRODUCT BRIDGE**:
  `4^a · d(2a−2) = 3^(2^(2a−2)) − 1` — the 3-world's power times the
  2-world's tower value at the matched index IS the maximal all-twos
  word: the product world `6^j = 2^j·3^j` in its killing form, the
  arithmetic face of the synchronized shadows. Axioms:
  `[propext, Quot.sound]`.
- `CardinalWorldsMirrorBridge` — **THE ABSORPTION-MIRROR BRIDGE**, the
  worlds' combination law (the chief of the other bridges): the 2-world
  and the 3-world share the one absorption tree of the 6-world (the
  synchronized shadows' CRT identification — `6^k`-resolution is exactly
  simultaneous `2^k`- and `3^k`-resolution). Two faces: a silent sheet
  cut word manufactures a silent 2-world tower value; a silent
  deep-class power manufactures one too.
- `hWave_of_postulateI_mirror` — **THE WAVE TRANSPORT**: Postulate I +
  the mirror bridge kill every silent sheet cut word.
- `hS0_of_postulateI_mirror` — **THE DEEP-CLASS TRANSPORT**: Postulate I
  + the mirror bridge kill every silent deep-class power.
- `four_power_omega_shadow_wave_tailF_of_postulateI` — **THE
  LAW-PROMOTION**: `hTailF` — the object that rode as the boundary
  hypothesis in `HC_Solution.lean` and `MonolithBoundary.lean` — is a
  THEOREM of the granted laws: **Postulate I** (the 2-world signature
  law) combined with the **absorption-mirror bridge**. The nine-clause
  second-observer conditional is consumed in full. **Postulate II is
  nowhere.** Axioms: `[propext, Classical.choice, Quot.sound]`.
- `erdos_even_conjecture_of_postulateI` — **THE CROWN UNDER THE GRANTED
  LAWS**: the even-exponent Erdős statement (`∀ K ≥ 8`,
  `noTernaryTwo (4^K) = false`) as a theorem of the two laws.
  Axioms: `[propext, Classical.choice, Quot.sound]`.

## THE BOUNDARY (the laws the derivation rests on)

1. **POSTULATE I** — `∀ j ≥ 2, hasTernaryTwo (d j) = true` — the
   2-world's signature law (the boss's grant). Its proven faces:
   `bridge_sig_even` (j even), `bridge_sig_j_mod6_3` (j ≡ 3 mod 6);
   its deep classes are the mirror of the Erdős tree (§2).
2. **THE ABSORPTION-MIRROR BRIDGE** — the worlds' combination law: a
   silent 3-world absorption manufactures a silent 2-world tower value.
   Its green faces in this module: `cardinal_worlds_mirror` (§3, the
   cascade-level duality), `four_pow_mul_d` (§8, the 6-world product),
   the mod-9 six-cycle correspondence (§2), and the synchronized-shadows
   CRT (the repo's `GSTGraphV2SixAdicSynchronizedShadows`).

Postulate II (the valuation bound) is banned and appears nowhere in the
module.

## CI ITERATION LEDGER (7 runs)

- run 1 (`35512108866`): 53 mechanical errors.
- run 2 (`35514823678`): 29 errors.
- run 3 (`35517139332`): 22 errors.
- run 4 (`35519564495`): 9 errors.
- run 5 (`35521907253`): **SUCCESS** — the slices module green.
- run 6 (`35540126783`): 1 error — `rw [← Nat.pow_mul]` on the literal
  base `4^a` (the pattern `(x^m)^n` does not match a literal base);
  fixed by normalizing the base first (`show 4 = 2^2`), the repo's own
  idiom.
- run 7 (`35542150111`): **SUCCESS** — the law-promotion green:
  comparator `Your solution is okay! / PASS`, axiom audit clean, all
  §8 theorems `[propext, Classical.choice, Quot.sound]`.
