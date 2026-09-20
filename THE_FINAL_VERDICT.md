# THE FINAL VERDICT — ErdosTernary2 Campaign Autopsy (Terminal Handoff)

**Date**: 2026-09-20
**Author**: Final analysis agent (post-SOL), with CI-verified receipts.
**Scope**: The complete dissection of the hTailF hypothesis → theorem conversion
mission, the map of every route opened after the mock-green era, and the exact
mathematical state of the remaining seam.

---

## 1. Executive verdict

1. **The remembered "complete green proof" never existed.** The Sept-10-13
   "green" runs passed `scripts/comparator.sh`, which prints
   `"Your solution is okay!"` after ANY clean build (mock). The REAL judge
   (`problem406-official-comparator.yml`, lean4export + official comparator
   binary, statement match + axiom gate) has been red in **0/20** runs, ever.
2. **The single remaining red link** in the binder-free route
   (`GSTResidualOmegaRevival` → `full_erdos`) is
   `GSTFinalPrefixOneDirectU2DCollision.canonical_perfect_power_block_collision_direct`
   — specifically its negative side
   `canonical_right_bad_forces_weighted_cross_nonpositive` (the `omega` at
   line 173 of that file).
3. **The negative-side proof strategy of the campaign handoff is REFUTED by
   counterexample** (this document, §4): the weighted-cross-prefix (WCP)
   nonpositivity lemma is FALSE at both the general-combinatorial level
   (4119/18829 = 21.9% violations among all-bad-right-edge rectangles) and
   the forced-prefix level (7556/31246 = 24.2% among `E = 1 + 3^b·T`
   rectangles with random `T`). No argument built only from
   right-edge badness + the rectangle identity + endpoint sign bounds can
   close it. **Any real proof must use the global arithmetic of the specific
   power tail** `T = 4^(3^(s+1)·n) / 3^(s+2)`.
4. **The collision theorem itself is TRUE** — verified numerically with
   **0 failures** across `s ∈ {1,2,3}`, `n ∈ {1..40}`, witness search to
   position 400 (§5). The theorem is not vacuous (the child premise holds in
   every tested case) and the conclusion holds in every tested case.
5. **The remaining seam is equivalent to the open Erdős ternary-2
   conjecture's core.** The chain of equivalences (all green implications
   except the one seam) is given in §3. Converting `hTailF` from hypothesis
   to theorem = proving that seam = proving the no-erasure/lift step of a
   45-year-old open problem (community-verified computationally to enormous
   bounds; proof open).

---

## 2. What is green and socketed (CI-verified inventory)

- **Odd arm**: `erdos_ternary_2_odd_universal` — trivial trit-0 = 2. Green.
- **Modular family** (green, unconditional): `even_case_a_mod3_2`
  (a ≡ 2 mod 3 → 4^a ≡ 7 mod 9 = 21₃), `even_case_a_0_div3_2`,
  `even_case_a_7_mod9`, `even_case_a_0_div3_1_mod9`.
- **Finite base**: `modular_check_base` (a ≤ 500). Green.
- **Pure x4 lift**: `gst_pure_lift_or_forced_cascade` (digit-2 of 4^(a−1)
  → digit-2 of 4^a). Green.
- **The atomic negative side**:
  `gst_prefix_one_no_parent_navigation_of_omega_bad_atomic` — omega-bad
  trace forbids the parent Navigation witness. Green (monolith line 8586).
- **The positive collision side**:
  `weightedCrossPrefix_positive_of_top_leading_happy` — top-row Happy
  column dominates (94·4^N + 149 ≤ 5·R vs 37·(1−4^N)·(3^K−1)/2 floors).
  Green (`GSTU2DSharpCrossingBlock`).
- **The connector**: `GSTFinalResidualConnector.residual_bad_trace_to_right_bad`
  — REPAIRED this session (2-line `rw [hseed]` bug; the seed
  `(4*1)/3^(s+k+1)` was never rewritten via `Nat.div_eq_of_lt`).
  Branch `astra/connector-repair`, commit `3eb07316`, CI run
  **35495944531 = SUCCESS**.
- **The WCP↔sum bridge**: `weightedCrossPrefix_eq_sum`
  (`GSTFinalPrefixOneStep6Boundary`, registered green) — connects the
  recursive `weightedCrossPrefix` to the rectangle sum. NOTE: this connects
  the SYNTAX, not the SIGN (see §4).
- **Controller stack**: `InfiniteBadCoupledControl`, `LatentGateTransfer`,
  `InfiniteCoupledLedger` past/future synchronization — all green.
- **Terminal packet**: `canonical_perfect_power_block_terminal_packet` —
  transports child-Happy + right-bad to the `graph 1` n-wave frame.
  Green, and deliberately does NOT assert a contradiction.

## 3. The equivalence map — every route lands on ONE seam

All of the following are green implications whose composition reduces the
even arm to ONE unproven statement (names as in the monolith/HEAD):

```
full_erdos (∀ n ≥ 9, noTernaryTwo (2^n) = false)
  ← the_act ← even_universal (a ≥ 5)
      ├─ a ≤ 500                 : GREEN (finite)
      ├─ a % 3 = 2               : GREEN (mod 9)
      ├─ a % 3 = 1               : GREEN reduction to a−1 (pure lift)
      └─ a % 3 = 0 (a = 3^s·b)   : four_power_good_witness_div_three
            ← navigation_all ← gst_navigation_witness_all_of_residual
            ← GSTResidualNavigationLift ← gst_residual_navigation_lift_of_prefix_one
            ← GSTPrefixOneNavigationLift                      *** THE SEAM ***
                 ≡ canonical_perfect_power_block_collision_direct   (revival route)
                 ≡ canonical_right_bad_forces_weighted_cross_nonpositive (WCP form)
                 ≡ four_power_happy_climb                        (astra TailF route)
                 ≡ ThirdWaveNoCommonDescent                      (multiscale route)
                 ≡ MahlerSharp + ResidualGhostCompression        (worldtrace route)
                 ≡ FourPowerCreationMaster → SeedOneWitness      (SeedCore route)
                 ≡ SeedOneWitness (prefixOffset s + 4^(3^s)·canonicalTail (s+1) n)
                                                               (cleanest form)
```

**Cleanest open-core statement** (one universal ∀, no side conditions beyond
s, n ≥ 1):

> For all `s ≥ 1`, `n ≥ 1`:
> `SeedOneWitness (prefixOffset s + 4^(3^s) · canonicalTail (s+1) n)`
> where `canonicalTail s b = 4^(3^s·b) / 3^(s+1)`,
> `prefixOffset s = (4^(3^s)/3^(s+1))/3`,
> `SeedOneWitness X = ∃ j, digit3 X j = 2 ∧ (1 + 4·(X % 3^j))/3^j ∈ {0, 3}`.

Equivalently (kernel decomposition, `gst_step6_collision_kernel`):
Navigation(child) → Navigation(parent) — the lift — while the negative side
(omega-bad → ¬Navigation(parent)) is green-atomic. The lift alone is missing.

**Why this is the open conjecture**: the exponents `3^s·b` (`b ≢ 0 mod 3`)
are exactly the even-arm exponents with v₃ ≥ 1; the lift is the induction
step of the strong induction over `s`; the base cases are finite/green.
Proving the lift closes Erdős ternary-2 — a problem open since the 1970s
(Erdős; last known exception 2^8 = 256 = 100111₃; no further exceptions
are known to enormous computational bounds; no proof is known).

## 4. THE REFUTATION RECEIPTS (new this session — campaign-defining)

The campaign handoff (`LEAN_FINAL_COLLISION_HANDOFF.md`) prescribed:
"use the controller ledger + rectangle identity + explicit endpoint sign
bounds" to prove WCP ≤ 0. **This strategy is refuted by counterexample**:

- **General rectangles** (`E` random, `N ∈ [2,7]`, window all-bad on row N):
  18829 qualifying rectangles; **4119 (21.9%) have WCP > 0**.
  Examples: `E=418, N=3, b=1, K=4 → WCP=32412`;
  `E=322, N=6, b=0, K=5 → WCP=2860974`.
- **Forced-prefix rectangles** (`E = 1 + 3^b·T`, `T` random — the LTE shape,
  `N = 3^s`, `b = s+2`): 31246 qualifying; **7556 (24.2%) have WCP > 0**.
  Examples: `s=2, T=101, K=3 → WCP=63113439`;
  `s=3, T=15, K=2 → WCP=1536697036036218966`.

Interpretation: WCP-nonpositivity under right-edge badness is FALSE at both
levels of generality below "T is the specific power tail". On canonical
rectangles the hypothesis is vacuous (the collision holds), so the theorem
is vacuously true — and that vacuousness is precisely the open content.
**No local/divergence argument can work; the proof must engage the global
arithmetic of `4^(3^(s+1)·n)`'s ternary digits.**

The twelve-state numeric search (prior session) already showed the only
per-cell sign-compatible chart is pure `crossDensity` (whose vertical
telescope carries the `84·surviveI` source); the survive-domination needed
to close its sign is the same open content. The synthetic counterexamples
above close the door on every weaker strategy.

## 5. Truth-evidence receipts (all reproducible; script in
`.verification/final_verdict_check.py`)

- **Collision theorem**: `s ∈ {1,2,3} × n ∈ {1..40}`, witness search to
  position 400: **0 counterexamples, 0 vacuous premises** (the child
  Navigation premise held in all 120 cases; the parent Happy conclusion
  held in all 120).
- **Lift positional structure**: child witness position `q` vs parent
  seed-one witness position `j`: differences range **−30…+40** with no
  local pattern — the transport is global (this kills any "one-step
  local lift" hope; measured on `s ∈ {1,2,3} × n ∈ {1..7}`).
- **Coverage map** for `a ∈ [501, 3000)` (even-arm exponents): the green
  modular family M1–M4 leaves 1018 uncovered; a 12-trit low-window check
  leaves only 22 (all caught by the full conjecture check). Erdős
  ternary-2 itself: **0 failures for n ∈ [9, 1200]**.

## 6. CI state at this writing

- `astra/connector-repair` @ `3eb07316`: Lean Action CI run 35495944531
  **SUCCESS** (the connector module now compiles clean; the second of the
  two probe failures is dead).
- Probe runs 35492244424 / 35493428992 (`astra/final-collision-probe`):
  the first failure (unregistered modules) was a lakefile registration gap;
  the second pinned the remaining failure to exactly
  `GSTFinalPrefixOneDirectU2DCollision.lean:173` (the WCP `omega`) —
  everything else in the never-compiled binder-free route compiles.
- The official comparator remains red for the structural reason documented
  here; a Solution wiring any hypothesis-based crown cannot pass its axiom
  gate.

## 7. The path for whoever attacks next

1. The seam to attack: `SeedOneWitness (z_s + 4^(3^s)·T)` for the specific
   power tail `T` (§3 cleanest form). Everything else is socketed and green.
2. The attack must be global-arithmetic (e.g., genuine equidistribution /
   carry-chain structure of `4^a` trits). Local divergence charts are
   refuted (§4). The survive-domination inequality is the analytic face.
3. Do NOT re-attempt: WCP ≤ 0 from badness+identity (refuted), mixedDensity
   combinations (per-cell infeasible: `mixed(3,0)=+168`), Mahler/third-wave
   re-derivations (all land on the same seam with more machinery).
4. Until the seam is proven, `hTailF`/`four_power_happy_climb` remains a
   hypothesis; the honest strongest artifact is the conditional crown +
   the green inventory in §2.
