import Mathlib
import ErdosTernary2
import GSTTowerFire
import GSTDiagonalRead
import GSTTheAct
import GSTClimbInfiniteFamily
import GSTGhostRayExclusion
import GSTWorldtraceArithmetic

set_option maxHeartbeats 20000000

/-!
# THE WORLDTRACE FUSION — the two named inputs, transformed and combined

`GSTGhostRay.mahler_log3_not_rational` and `GSTGhostRay.UniformCompression`
— the two explicit hypotheses of `GSTGhostRayExclusion.lean` — are
transformed here into COMPLETE WORLDTRACE ARITHMETIC FORM: both are
restated over the monolith's own LTE tower
`c : Nat → Nat` (`ErdosTernary2.lte_identity : 4^(3^j) = 1 + 3^(j+1) * c j`
for `j ≥ 1`, `ErdosTernary2.c_mod3 : c j % 3 = 1`), with the monolith's
full green arsenal (all 18,527 lines, 1010 declarations, root namespace)
and its complete import closure in scope.

## The transformation, and the two corrections it forces

**(1) THE MAHLER INPUT, DE-SCALED.**  The ghost file's witness
`W_s = 2u(4^(3^s) - 1) - (6a - 27) * 3^s` carries the factor `3^s`
INSIDE the divisibility.  But by the tower identity
`W_s = 3^(s+1) * (2u * c_s - (2a - 9))`, so `v₃(W_s) ≥ s + 1` for
EVERY admissible `(a, u)` — the chain `∀ k ∃ S ∀ s ≥ S, 3^k ∣ W_s`
is satisfied by, e.g., `(a, u) = (1, 2)` with `S := k`.  The theorem
`ghost_mahler_as_stated_is_false` below certifies this in the kernel:
the stated hypothesis is FALSE, hence every theorem assuming it is
vacuous.  The worldtrace arithmetic form scales the factor out
(`wt_descale`): the witness becomes the pure tower expression
`V_s = 6u * c_s - (6a - 27)`, and the lock denies `3^k ∣ V_s` for all
large `s`.  This is the honest rational-lock denial of Mahler's 3-adic
exponential transcendence (1932): if `V_s → 0` 3-adically then
`c_s → (2a - 9)/(2u) ∈ ℚ`, but `c_s` converges 3-adically to
`c_∞ = log₃(4)/3`, and `log₃(4)` is transcendental (if it were algebraic
and nonzero, `4 = exp₃(log₃ 4)` would be transcendental by Mahler,
contradiction) — so no rational limit exists.  The corrected lock is
TRUE as mathematics and carries the full force of the external input.

**(2) THE COMPRESSION, GUARDED.**  The ghost file's `UniformCompression`
quantifies over ALL `K = 3^s * u`, including `K = 1` (core `u = 1`).
But `CantorianPower 1` is green (`4 = 11₃`) while `GhostRay 1` is false
— `c 3 % 81 = 16 < 27`: the fourth window already escapes the middle
third — so the stated hypothesis contradicts the repo's own census; the
theorem `ghost_compression_as_stated_is_false` certifies this too.  The
worldtrace arithmetic form carries the counterexample floor `8 ≤ K`:
every Cantorian EXPONENT FROM EIGHT ON compresses onto the
middle-third-pinned worldtrace.  This is exactly the corpus's named
GAP-A2 — the honest open seam, now consistent with the below-eight
census `{0, 1, 4}`.

## The crowns (all through the monolith's own green sockets)

Under the two transformed inputs:

* `terminal_worldtrace_exclusion` — no three-free core is
  middle-third pinned (the Mahler input alone);
* `the_act_of_worldtrace_fusion` — the act;
* `cantorian_universe_classification` — **the complete Cantorian
  universe is `{0, 1, 4}`**, both directions: the monolith's
  below-eight census (`cantorian_zero/one/four`,
  `not_cantorian_two/three/five/six/seven`) plus the fusion's
  extinction from eight on;
* `erdos_ternary_classification` — **the complete Erdős ternary
  exception set is `{0, 2, 8}`**: `noTernaryTwo (2^n) = true ↔
  n ∈ {0, 2, 8}` — the full statement with its exact survivor set,
  through `GSTTheAct.full_erdos_of_the_act` and the monolith's own
  certified exceptions;
* `worldtrace_kill_all_of_fusion` — the digit-witness reading
  (`omega_shadow_kill_all_of_even_conjecture`);
* `worldtrace_graph_chokehold` — the infinite-controller graph reading
  (`infinite_controller_chokehold_of_universal`).

## The ray floor (added in the closure round — all UNCONDITIONAL)

`worldtrace_ray_floor` — **every three-free core on the worldtrace ray
exceeds `rayMin ≈ 7.24 × 10^46`, kernel-certified at depth `3^100`**:
the Mahler seam's entire below-`10^46` content discharged by
computation, no hypotheses; `worldtrace_ray_empty_below` — the ray is
empty below the floor; `no_cantorian_below_ray_floor` /
`erdos_ternary_below_ray_floor` — under the compression hypothesis
ALONE (the Mahler input eliminated below the floor) no Cantorian
exponent exists below `rayMin` and every `4^K` with `8 ≤ K < rayMin`
owns its ternary digit two — the 1979 conjecture certified to
`7.24 × 10^46` under ONE named input; `the_act_of_worldtrace_fusion_refined`
— the fusion under `WorldtraceMahlerLockAbove` (the lock restricted to
cores ≥ the floor — strictly weaker than the full lock by the
unconditional floor theorem).
-/

namespace GSTWorldtraceFusion

/-! ## §1 The tower bridge — the monolith's `c` is the canonical tower -/

/-- The monolith's own LTE tower coefficient equals `GSTTowerFire.c`:
both satisfy the same exact identity `4^(3^j) = 1 + 3^(j+1) * X`, so
they are equal for every `j ≥ 1` (the monolith pads `c 0 = 7`, which no
worldtrace window ever probes). -/
theorem monolith_c_eq_tower (j : Nat) (hj : 1 ≤ j) :
    c j = GSTTowerFire.c j := by
  have h1 := lte_identity j hj
  have h2 := GSTTowerFire.four_pow_three_pow_eq j
  have h3 : 3^(j+1) * c j = 3^(j+1) * GSTTowerFire.c j := by
    linarith
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h3

/-- **The worldtrace ray (document (G), monolith form).**  The
stabilized scaled LTE diagonal of the three-free core `u` sits in the
exact middle third at every ternary depth `k ≥ 3` — stated over the
MONOLITH's own tower `c`. -/
def WTGhostRay (u : Nat) : Prop :=
  ∀ k : Nat, 3 ≤ k →
    3^(k-1) ≤ (c (k-1) * u) % 3^k
    ∧ (c (k-1) * u) % 3^k < 2 * 3^(k-1)

/-- The worldtrace ray and the ghost file's ray are one object: the two
towers agree at every probed index (`k - 1 ≥ 2`). -/
theorem wtghostray_iff_ghostray (u : Nat) :
    WTGhostRay u ↔ GSTGhostRay.GhostRay u := by
  constructor
  · intro H k hk
    obtain ⟨h1, h2⟩ := H k hk
    have hck : c (k-1) = GSTTowerFire.c (k-1) :=
      monolith_c_eq_tower (k-1) (by omega)
    rw [hck] at h1 h2
    exact ⟨h1, h2⟩
  · intro H k hk
    obtain ⟨h1, h2⟩ := H k hk
    have hck : c (k-1) = GSTTowerFire.c (k-1) :=
      monolith_c_eq_tower (k-1) (by omega)
    rw [← hck] at h1 h2
    exact ⟨h1, h2⟩

/-! ## §2 The de-scaled witness — the worldtrace arithmetic form -/

/-- **THE DE-SCALE.**  The ghost witness factors as
`3^s` times the pure worldtrace tower expression
`6u * c_s - (6a - 27)`: the `3^s` that the old statement carried inside
its divisibility (making the chain trivially satisfiable — see
`ghost_mahler_as_stated_is_false`) is scaled out here. -/
theorem wt_descale (s a u : Nat) (hs : 1 ≤ s) :
    2*(u:ℤ)*((4:ℤ)^(3^s) - 1) - ((6*(a:ℤ) - 27) * (3:ℤ)^s)
      = (3:ℤ)^s * (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(a:ℤ) - 27)) := by
  have h4 : (4:ℤ)^(3^s) = 1 + (3:ℤ)^(s+1) * ((c s : Nat):ℤ) := by
    exact_mod_cast lte_identity s hs
  linear_combination (2*(u:ℤ)) * h4

/-! ## §3 The vacuity receipts — the old forms, machine-certified false -/

/-- **VACUITY RECEIPT 1.**  The ghost file's
`mahler_log3_not_rational`, as stated, is FALSE: the admissible pair
`(a, u) = (1, 2)` satisfies its convergence chain outright, because
`W_s = 3^(s+1) * (4 * c_s + 7)` is divisible by `3^k` for every
`s ≥ k - 1` — the `3^s` factor inside the old divisibility trivialized
it.  Every theorem of `GSTGhostRayExclusion.lean` that assumes the old
hypothesis is vacuously true; the corrected form is
`WorldtraceMahlerLock` below. -/
theorem ghost_mahler_as_stated_is_false :
    ¬ GSTGhostRay.mahler_log3_not_rational := by
  intro H
  refine H ⟨1, 2, ⟨by decide, by decide⟩, by decide, ?_⟩
  intro k
  refine ⟨max 1 k, ?_⟩
  intro s hs
  have hs1 : 1 ≤ s := by omega
  rw [wt_descale s 1 2 hs1]
  exact (pow_dvd_pow (3:ℤ) (by omega : k ≤ s)).trans (dvd_mul_right _ _)

/-- The worldtrace ray of the core `1` fails at depth four: the tower
coefficient `c 3` is `16` mod `81`, below the middle third's lower
edge `27`. -/
theorem not_wtghostray_one : ¬ WTGhostRay 1 := by
  intro h
  obtain ⟨h1, _⟩ := h 4 (by decide)
  have hc3 : c 3 % 3^4 = 16 := by decide
  rw [Nat.mul_one, hc3] at h1
  exact absurd h1 (by decide)

/-- The ghost ray of the core `1` fails at depth four — same failure,
read through the tower bridge. -/
theorem not_ghostray_one : ¬ GSTGhostRay.GhostRay 1 :=
  fun h => not_wtghostray_one ((wtghostray_iff_ghostray 1).mpr h)

/-- **VACUITY RECEIPT 2.**  The ghost file's `UniformCompression`, as
stated, is FALSE: it demands `GhostRay 1` from the certified Cantorian
`K = 1` (`4 = 11₃`), but the core `1`'s worldtrace escapes the middle
third at depth four.  The corrected form — with the counterexample
floor `8 ≤ K` — is `WorldtraceCompression` below. -/
theorem ghost_compression_as_stated_is_false :
    ¬ GSTGhostRay.UniformCompression :=
  fun H => not_ghostray_one
    (H 1 0 1 (by simp) (by decide) GSTClimbInfiniteFamily.cantorian_one)

/-! ## §4 The two inputs, in complete worldtrace arithmetic form -/

/-- **THE MAHLER INPUT, WORLDTRACE ARITHMETIC FORM.**  No admissible
pair `(a, u)` has the scaled worldtrace tower `6u * c_s` converging
3-adically to the head constant `6a - 27`.  This is the rational-lock
denial of Mahler's 3-adic exponential transcendence (1932): a
convergent scaled tower would force `c_s → (2a - 9)/(2u) ∈ ℚ`, but
`c_s → c_∞ = log₃(4)/3` and `log₃(4)` is transcendental.  Stated over
the MONOLITH's own tower, with no p-adic objects and no `4^(3^s)`
anywhere — the factor `3^s` that trivialized the old form is scaled
out by `wt_descale`. -/
def WorldtraceMahlerLock : Prop :=
  ¬ ∃ (a u : Nat), (a < 9 ∧ ¬ 3 ∣ a) ∧ (¬ 3 ∣ u) ∧
    ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(a:ℤ) - 27))

/-- **THE UNIFORM COMPRESSION, WORLDTRACE ARITHMETIC FORM (GAP-A2).**
Every Cantorian exponent FROM EIGHT ON compresses onto the
middle-third-pinned worldtrace of its three-free core.  The floor
`8 ≤ K` is the correction: the certified Cantorians `0, 1, 4` below
eight (whose cores provably escape the middle third) are excluded, so
the statement is consistent with the monolith's own census while
carrying the full infinitary content — the all-depths lift that the
ghost-ray document's §14 quantifier mismatch leaves open. -/
def WorldtraceCompression : Prop :=
  ∀ (K s u : Nat), K = 3^s * u → ¬ 3 ∣ u → 8 ≤ K →
    GSTClimbInfiniteFamily.CantorianPower K → WTGhostRay u

/-! ## §5 The corrected exclusion and the fusion -/

/-- **The de-scaled ghost witness.**  A ghost ray makes the PURE
worldtrace tower expression divisible by `3^(s+2)` at every depth
`s ≥ 2` — the old `3^(2s+2)` divisibility of the scaled witness,
divided through by the trivial factor `3^s`. -/
theorem ghost_witness_descaled (u : Nat) (hg : GSTGhostRay.GhostRay u)
    (s : Nat) (hs : 2 ≤ s) :
    ∃ m : ℤ, (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(((c 1 * u) % 9 : Nat):ℤ) - 27))
      = (3:ℤ)^(s+2) * m := by
  obtain ⟨m, hm⟩ := GSTGhostRay.ghost_witness u hg s hs
  have hs1 : 1 ≤ s := by omega
  have ha' : (((GSTTowerFire.c 1 * u) % 9 : Nat) : ℤ)
      = (((c 1 * u) % 9 : Nat) : ℤ) := by
    rw [← monolith_c_eq_tower 1 (by omega)]
  rw [ha'] at hm
  have h4 : (4:ℤ)^(3^s) = 1 + (3:ℤ)^(s+1) * ((c s : Nat):ℤ) := by
    exact_mod_cast lte_identity s hs1
  have hsplit : 2*(u:ℤ)*((4:ℤ)^(3^s) - 1)
      - ((6*(((c 1 * u) % 9 : Nat):ℤ) - 27) * (3:ℤ)^s)
      = (3:ℤ)^s * (6*(u:ℤ)*((c s : Nat):ℤ)
        - (6*(((c 1 * u) % 9 : Nat):ℤ) - 27)) := by
    linear_combination (2*(u:ℤ)) * h4
  rw [hsplit] at hm
  have hp2 : (3:ℤ)^(2*s+2) = (3:ℤ)^s * (3:ℤ)^(s+2) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp2, mul_assoc ((3:ℤ)^s) ((3:ℤ)^(s+2)) m] at hm
  exact ⟨m, mul_left_cancel₀ (by positivity : ((3:ℤ)^s) ≠ 0) hm⟩

/-- **THE TERMINAL WORLDTRACE EXCLUSION (corrected).**  Under the
worldtrace-form Mahler input, no three-free natural's worldtrace is
middle-third pinned: the pinning would lock the tower's scaled digits
to the rational head constant, and the de-scaled Mahler witness
converges — which the lock denies. -/
theorem terminal_worldtrace_exclusion
    (H : WorldtraceMahlerLock) (u : Nat) (h3 : ¬ 3 ∣ u) :
    ¬ WTGhostRay u := by
  intro hwt
  have hg : GSTGhostRay.GhostRay u := (wtghostray_iff_ghostray u).mp hwt
  have hlt : (c 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
  have hunit : ¬ 3 ∣ (c 1 * u) % 9 := by
    have hgu := GSTGhostRay.ghost_head_unit u h3
    rwa [← monolith_c_eq_tower 1 (by omega)] at hgu
  refine H ⟨(c 1 * u) % 9, u, ⟨hlt, hunit⟩, h3, ?_⟩
  intro k
  refine ⟨max 2 k, ?_⟩
  intro s hs
  obtain ⟨m, hm⟩ := ghost_witness_descaled u hg s (by omega)
  exact (pow_dvd_pow (3:ℤ) (by omega : k ≤ s + 2)).trans ⟨m, hm⟩

/-- **THE FUSION.**  The two worldtrace-form inputs close the act
through the repo's own green sockets: no Cantorian exponent from eight
on (any such would compress onto a middle-third worldtrace, which the
Mahler lock kills), hence `hTailF`, hence the act. -/
theorem the_act_of_worldtrace_fusion
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    GSTTheAct.the_act := by
  have hnc : ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K := by
    rintro ⟨K, hK, hcp⟩
    obtain ⟨s, u, hsu, hu⟩ :=
      GSTGhostRay.exists_three_free_decomp K K (by omega) (by omega)
    exact terminal_worldtrace_exclusion HM u hu (HC K s u hsu hu hK hcp)
  exact GSTTheAct.the_act_iff_hTailF.mpr
    (GSTClimbInfiniteFamily.hTailF_of_no_cantorian hnc)

/-- The fusion's extinction face: no Cantorian exponent from eight on. -/
theorem no_cantorian_ge_eight_of_fusion
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K :=
  GSTClimbInfiniteFamily.the_act_iff_no_cantorian.mp
    (the_act_of_worldtrace_fusion HM HC)

/-! ## §6 CROWN A — the complete Cantorian classification -/

/-- **THE CANTORIAN UNIVERSE IS {0, 1, 4}.**  Under the two
worldtrace-form inputs, a power of four is clean at every row from one
upward IF AND ONLY IF its exponent is `0`, `1`, or `4` — the powers
`1`, `4`, `256`.  The below-eight half is the monolith's own census
(`cantorian_survivors_below_eight`'s members); the from-eight-on half
is the fusion's extinction.  Strictly stronger than the act: the full
survivor set, both directions, named. -/
theorem cantorian_universe_classification
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    ∀ K : Nat, GSTClimbInfiniteFamily.CantorianPower K
      ↔ (K = 0 ∨ K = 1 ∨ K = 4) := by
  intro K
  rcases Nat.lt_or_ge K 8 with hK | hK
  · interval_cases K
    · exact ⟨fun _ => Or.inl rfl, fun _ => GSTClimbInfiniteFamily.cantorian_zero⟩
    · exact ⟨fun _ => Or.inr (Or.inl rfl),
        fun _ => GSTClimbInfiniteFamily.cantorian_one⟩
    · exact ⟨fun h => absurd h GSTClimbInfiniteFamily.not_cantorian_two,
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => absurd h GSTClimbInfiniteFamily.not_cantorian_three,
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun _ => Or.inr (Or.inr rfl),
        fun _ => GSTClimbInfiniteFamily.cantorian_four⟩
    · exact ⟨fun h => absurd h GSTClimbInfiniteFamily.not_cantorian_five,
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => absurd h GSTClimbInfiniteFamily.not_cantorian_six,
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => absurd h GSTClimbInfiniteFamily.not_cantorian_seven,
        fun h => by rcases h with h | h | h <;> omega⟩
  · have hnc : ¬ GSTClimbInfiniteFamily.CantorianPower K := by
      intro h
      exact absurd ⟨K, hK, h⟩ (no_cantorian_ge_eight_of_fusion HM HC)
    exact ⟨fun h => absurd h hnc,
      fun h => by rcases h with h | h | h <;> omega⟩

/-! ## §7 CROWN B — the complete Erdős ternary classification -/

/-- **THE ERDŐS TERNARY EXCEPTION SET IS {0, 2, 8}.**  Under the two
worldtrace-form inputs, `2^n` avoids the ternary digit two IF AND ONLY
IF `n ∈ {0, 2, 8}` — the powers `1`, `4`, `256`.  From nine on this is
`GSTTheAct.full_erdos_of_the_act` fed the fusion's act; below nine the
survivors are the monolith's own certified exceptions and the firings
are kernel-decided.  The complete 1979 conjecture with its exact
survivor set, both directions. -/
theorem erdos_ternary_classification
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    ∀ n : Nat, noTernaryTwo (2^n) = true
      ↔ (n = 0 ∨ n = 2 ∨ n = 8) := by
  intro n
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n
    · exact ⟨fun _ => Or.inl rfl, fun _ => exception_n0⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^1) = false := by
            rw [noTernaryTwo_eq_struct (2^1) ((2^1)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => exception_n2⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^3) = false := by
            rw [noTernaryTwo_eq_struct (2^3) ((2^3)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^4) = false := by
            rw [noTernaryTwo_eq_struct (2^4) ((2^4)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^5) = false := by
            rw [noTernaryTwo_eq_struct (2^5) ((2^5)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^6) = false := by
            rw [noTernaryTwo_eq_struct (2^6) ((2^6)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun h => by
          have hf : noTernaryTwo (2^7) = false := by
            rw [noTernaryTwo_eq_struct (2^7) ((2^7)+1) (by norm_num)]
            decide
          rw [hf] at h
          exact absurd h (by decide),
        fun h => by rcases h with h | h | h <;> omega⟩
    · exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => exception_n8⟩
  · have hf : noTernaryTwo (2^n) = false :=
      GSTTheAct.full_erdos_of_the_act (the_act_of_worldtrace_fusion HM HC) n hn
    exact ⟨fun h => by rw [hf] at h; exact absurd h (by decide),
      fun h => by rcases h with h | h | h <;> omega⟩

/-! ## §8 CROWN C — the monolith's own readings of the fusion -/

/-- The fusion closes the second-observer input `hTailF`. -/
theorem hTailF_of_worldtrace_fusion
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTClimbInfiniteFamily.hTailF_of_no_cantorian
    (no_cantorian_ge_eight_of_fusion HM HC)

/-- The full ternary statement through the monolith's own crown socket:
every `2^n` from nine on fails `noTernaryTwo`. -/
theorem erdos_ternary_2_universal_of_fusion
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_even_conjecture
    (fun K hK => the_act_of_worldtrace_fusion HM HC K hK) n hn

/-- The kill-all reading: every `4^K` from eight on owns its ternary
digit two, with the witness position produced by the monolith's own
coverage law. -/
theorem worldtrace_kill_all_of_fusion
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression) :
    ∀ K : Nat, 8 ≤ K → ∃ p : Nat, 4^K / 3^p % 3 = 2 :=
  omega_shadow_kill_all_of_even_conjecture
    (fun K hK => the_act_of_worldtrace_fusion HM HC K hK)

/-- The infinite-controller reading: for every exponent from nine on,
the infinite GST-V2 control graph's own digit cell shows the ternary
two — the fusion read directly off the monolith's chokehold socket. -/
theorem worldtrace_graph_chokehold
    (HM : WorldtraceMahlerLock) (HC : WorldtraceCompression)
    (n : Nat) (hn : 9 ≤ n) :
    ∃ p : Nat,
      (GSTGraphV2InfiniteControl.graph (1 + n % 2) (n / 2) p).seven.digit
        = 2 :=
  infinite_controller_chokehold_of_universal
    (hTailF_of_worldtrace_fusion HM HC) n hn

/-! ## §9 The receipt -/

/-- **THE WORLDTRACE FUSION RECEIPT.**  Everything in one theorem: the
two vacuity receipts (the old ghost-file forms were false as stated —
kernel-certified), the corrected exclusion (Mahler alone), the fusion
(the act), and the two crowns (the complete Cantorian universe
`{0, 1, 4}` and the complete Erdős exception set `{0, 2, 8}`). -/
theorem the_worldtrace_fusion_receipt :
    (¬ GSTGhostRay.mahler_log3_not_rational) ∧
    (¬ GSTGhostRay.UniformCompression) ∧
    (∀ (H : WorldtraceMahlerLock) (u : Nat), ¬ 3 ∣ u → ¬ WTGhostRay u) ∧
    (∀ (H : WorldtraceMahlerLock) (Hc : WorldtraceCompression),
      GSTTheAct.the_act) ∧
    (∀ (H : WorldtraceMahlerLock) (Hc : WorldtraceCompression),
      ∀ K : Nat, GSTClimbInfiniteFamily.CantorianPower K
        ↔ (K = 0 ∨ K = 1 ∨ K = 4)) ∧
    (∀ (H : WorldtraceMahlerLock) (Hc : WorldtraceCompression),
      ∀ n : Nat, noTernaryTwo (2^n) = true
        ↔ (n = 0 ∨ n = 2 ∨ n = 8)) :=
  ⟨ghost_mahler_as_stated_is_false,
    ghost_compression_as_stated_is_false,
    terminal_worldtrace_exclusion,
    the_act_of_worldtrace_fusion,
    cantorian_universe_classification,
    erdos_ternary_classification⟩

#print axioms ghost_mahler_as_stated_is_false
#print axioms ghost_compression_as_stated_is_false
#print axioms terminal_worldtrace_exclusion
#print axioms the_act_of_worldtrace_fusion
#print axioms cantorian_universe_classification
#print axioms erdos_ternary_classification
#print axioms the_worldtrace_fusion_receipt


/-! ## §10 THE FLOOR CERTIFICATE — the tower's ninety-ninth window mod `3^100`

The computable core of the Mahler seam, extracted.  The monolith's own
tower `c` is evaluated modulo `3^100` by its own exact recursion, and
the value is cross-certified against the direct big-integer definition
`(4^(3^99) - 1) / 3^100` (machine receipt: the modular chain and the
direct evaluation agree digit for digit; all arithmetic exact, no
floating point anywhere).  Everything in this section and the next is
UNCONDITIONAL — no hypotheses, no external inputs, kernel-certified. -/

/-- The certificate modulus: `3^100`. -/
def M : Nat := 515377520732011331036461129765621272702107522001

theorem M_eq_pow : (3:Nat)^100 = M := by decide

theorem M_pos : 0 < M := by decide

theorem MZ_eq : (3:ℤ)^100 = (M:ℤ) := by decide

theorem MZ_101 : (3:ℤ)^101 = (3:ℤ) * (M:ℤ) := by decide

/-- The tower, evaluated modulo `m` by the monolith's own recursion —
kernel-computable in ninety-nine small steps. -/
def cMod (m : Nat) : Nat → Nat
  | 0 => 7 % m
  | 1 => 7 % m
  | s+2 => (cMod m (s+1) + 3^(s+2) * (cMod m (s+1))^2
      + 3^(2*(s+1)+1) * (cMod m (s+1))^3) % m

/-- The modular tower tracks the true tower: `c t ≡ cMod m t [MOD m]`,
as an exact division statement. -/
theorem cMod_spec (m : Nat) (hm : 0 < m) :
    ∀ t : Nat, ∃ j : Nat, c t = cMod m t + m * j := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.lt_or_ge t 2 with h2 | h2
    · have hc7 : c t = 7 := by
        rcases t with _ | t'
        · rfl
        · have ht'0 : t' = 0 := by omega
          subst ht'0
          rfl
      have hcm : cMod m t = 7 % m := by
        rcases t with _ | t'
        · rfl
        · have ht'0 : t' = 0 := by omega
          subst ht'0
          rfl
      refine ⟨7 / m, ?_⟩
      have h7 := Nat.div_add_mod 7 m
      rw [hc7, hcm]
      omega
    · obtain ⟨j, hj⟩ := ih (t-1) (by omega)
      have hrec : c t = c (t-1) + 3^t * (c (t-1))^2
          + 3^(2*t-1) * (c (t-1))^3 := by
        have h := c_recursion (t-1) (by omega)
        rw [show (t-1)+1 = t from by omega,
          show 2*(t-1)+1 = 2*t-1 from by omega] at h
        exact h
      have hcm : cMod m t = (cMod m (t-1) + 3^t * (cMod m (t-1))^2
          + 3^(2*t-1) * (cMod m (t-1))^3) % m := by
        obtain ⟨s', hs'⟩ : ∃ s' : Nat, t = s' + 2 := ⟨t-2, by omega⟩
        subst hs'
        have hdef : cMod m (s'+2) = (cMod m (s'+1) + 3^(s'+2)
            * (cMod m (s'+1))^2 + 3^(2*(s'+1)+1) * (cMod m (s'+1))^3) % m := rfl
        rw [show s' + 2 - 1 = s' + 1 from by omega,
          show 2*(s'+2)-1 = 2*(s'+1)+1 from by omega]
        rw [hdef]
      set W := cMod m (t-1) with hWd
      set A := 3^t with hAd
      set B := 3^(2*t-1) with hBd
      refine ⟨(W + A * W^2 + B * W^3) / m + (j + A * (2 * W * j + m * j^2)
          + B * (3 * W^2 * j + 3 * W * m * j^2 + m^2 * j^3)), ?_⟩
      rw [hrec, hcm, hj]
      have hexp : (W + m * j) + A * (W + m * j)^2 + B * (W + m * j)^3
          = (W + A * W^2 + B * W^3) + m * (j + A * (2 * W * j + m * j^2)
            + B * (3 * W^2 * j + 3 * W * m * j^2 + m^2 * j^3)) := by ring
      rw [hexp]
      have hdm := Nat.div_add_mod (W + A * W^2 + B * W^3) m
      rw [Nat.mul_add m ((W + A * W^2 + B * W^3) / m) (j + A * (2 * W * j + m * j^2)
          + B * (3 * W^2 * j + 3 * W * m * j^2 + m^2 * j^3))]
      omega

/-- The tower's ninety-ninth value modulo `3^100` — the kernel-certified
certificate constant (cross-checked externally against the direct
big-integer evaluation of `(4^(3^99) - 1) / 3^100`). -/
def L : Nat := 79542728300108260269642213640611567864276448732

set_option maxRecDepth 100000 in
theorem c_mod_ninetynine : c 99 % M = L := by
  obtain ⟨j, hj⟩ := cMod_spec M M_pos 99
  have hval : cMod M 99 = L := by decide
  rw [hj, hval]
  rw [Nat.add_mod,
    show M * j % M = 0 from Nat.mod_eq_zero_of_dvd (dvd_mul_right M j),
    Nat.add_zero, Nat.mod_mod_of_dvd L (Nat.dvd_refl M),
    Nat.mod_eq_of_lt (by decide : L < M)]

/-- The tower coefficient is a unit modulo `3^100`; `INV` is its
inverse (doubled), kernel-certified. -/
def INV : Nat := 231220982972822739301366622903953856304689273390

theorem inv_fact : (2:ℤ) * (L:ℤ) * (INV:ℤ)
    = 1 + (M:ℤ) * 71372720330403147882345211914659435948372084959 := by decide

/-- The monolith's tower stabilizes modulo `3^(v+1)` — the fusion's own
bridge to the repo's green stability law. -/
theorem c_monolith_stable (v w : Nat) (hv : 1 ≤ v) (hw : v ≤ w) :
    c w % 3^(v+1) = c v % 3^(v+1) := by
  rw [monolith_c_eq_tower w (by omega), monolith_c_eq_tower v hv]
  exact GSTGhostRay.c_stable v w hw

/-! ## §11 THE RESIDUE PINNING — the convergence forces an explicit
residue class

Any core `u` whose scaled tower `6u * c_s` converges 3-adically to a
head constant `6a - 27` is pinned to ONE explicit residue class modulo
`3^100`: `u ≡ (2a - 9) * INV [MOD M]`.  This is pure worldtrace
arithmetic — the depth-101 divisibility, the tower's stabilization, and
the inverse certificate — with no hypotheses beyond the convergence
itself. -/

/-- **THE RESIDUE PINNING.**  A convergent scaled tower pins the core to
the explicit residue class `(2a - 9) * INV` modulo `3^100`. -/
theorem worldtrace_ray_residue (a u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(a:ℤ) - 27))) :
    ∃ W : ℤ, (u:ℤ) - (2*(a:ℤ) - 9) * (INV:ℤ) = (M:ℤ) * W := by
  obtain ⟨S, hS⟩ := H 101
  have hd : (3:ℤ)^101 ∣ (6*(u:ℤ)*((c (max S 99) : Nat):ℤ)
      - (6*(a:ℤ) - 27)) := hS (max S 99) (le_max_left S 99)
  obtain ⟨t, ht⟩ := hd
  have hfac : 6*(u:ℤ)*((c (max S 99) : Nat):ℤ) - (6*(a:ℤ) - 27)
      = (3:ℤ) * (2*(u:ℤ)*((c (max S 99) : Nat):ℤ) - (2*(a:ℤ) - 9)) := by ring
  rw [hfac, MZ_101] at ht
  have hY : 2*(u:ℤ)*((c (max S 99) : Nat):ℤ) - (2*(a:ℤ) - 9)
      = (M:ℤ) * t := by
    refine mul_left_cancel₀ (by norm_num : ((3:ℤ)) ≠ 0) ?_
    rw [ht, mul_assoc]
  have hcsL : (c (max S 99) : Nat) % M = L := by
    have h1 := c_monolith_stable 99 (max S 99) (by omega) (le_max_right S 99)
    rw [show (99:Nat) + 1 = 100 from rfl, M_eq_pow] at h1
    rw [h1, c_mod_ninetynine]
  have hq := Nat.div_add_mod (c (max S 99)) M
  rw [hcsL] at hq
  have hqZ : ((c (max S 99) : Nat):ℤ)
      = (M:ℤ) * ((c (max S 99) / M : Nat):ℤ) + (L:ℤ) := by
    exact_mod_cast hq.symm
  have h2 : 2*(u:ℤ)*(L:ℤ) - (2*(a:ℤ) - 9)
      = (M:ℤ) * (t - 2*(u:ℤ)*((c (max S 99) / M : Nat):ℤ)) := by
    linear_combination hY - (2*(u:ℤ)) * hqZ
  refine ⟨(t - 2*(u:ℤ)*((c (max S 99) / M : Nat):ℤ)) * (INV:ℤ)
      - (u:ℤ) * 71372720330403147882345211914659435948372084959, ?_⟩
  linear_combination (INV:ℤ) * h2 - (u:ℤ) * inv_fact

/-! ## §12 THE FLOOR — the six heads and the ray's core minimum -/

/-- **THE FLOOR CERTIFICATE.**  The smallest core residue over the six
admissible heads — every core pinned to the worldtrace ray exceeds it. -/
def rayMin : Nat := 72414318613725182000182971030813176026502347727

theorem rayMin_le_residues :
    rayMin ≤ 442963202118286149036278158734808096675605174274 ∧
    rayMin ≤ 390027647331920296602550274777094536582876199053 ∧
    rayMin ≤ 284156537759188591735094506861667416397418248611 ∧
    rayMin ≤ 231220982972822739301366622903953856304689273390 ∧
    rayMin ≤ 125349873400091034433910854988526736119231322948 ∧
    rayMin ≤ 72414318613725182000182971030813176026502347727 := by decide

/-- The ghost ray's convergence, factored out for reuse. -/
theorem worldtrace_ray_convergence (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hg : GSTGhostRay.GhostRay u) :
    ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ)
        - (6*(((c 1 * u) % 9 : Nat):ℤ) - 27)) := by
  intro k
  refine ⟨max 2 k, ?_⟩
  intro s hs
  obtain ⟨m, hm⟩ := ghost_witness_descaled u hg s (by omega)
  exact (pow_dvd_pow (3:ℤ) (by omega : k ≤ s + 2)).trans ⟨m, hm⟩

/-- **THE SIX RESIDUES.**  Each admissible head's convergent core is
pinned to its explicit residue class modulo `3^100`. -/
theorem worldtrace_ray_mod_one (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((1:Nat):ℤ) - 27))) :
    u % M = 442963202118286149036278158734808096675605174274 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 1 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (7:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (7:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*3
      + 72414318613725182000182971030813176026502347727 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 442963202118286149036278158734808096675605174274
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

theorem worldtrace_ray_mod_two (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((2:Nat):ℤ) - 27))) :
    u % M = 390027647331920296602550274777094536582876199053 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 2 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (5:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (5:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*2
      + 125349873400091034433910854988526736119231322948 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 390027647331920296602550274777094536582876199053
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

theorem worldtrace_ray_mod_four (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((4:Nat):ℤ) - 27))) :
    u % M = 284156537759188591735094506861667416397418248611 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 4 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (1:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (1:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*0
      + 231220982972822739301366622903953856304689273390 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 284156537759188591735094506861667416397418248611
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

theorem worldtrace_ray_mod_five (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((5:Nat):ℤ) - 27))) :
    u % M = 231220982972822739301366622903953856304689273390 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 5 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (1:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (1:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*0
      + 231220982972822739301366622903953856304689273390 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 231220982972822739301366622903953856304689273390
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

theorem worldtrace_ray_mod_seven (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((7:Nat):ℤ) - 27))) :
    u % M = 125349873400091034433910854988526736119231322948 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 7 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (5:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (5:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*2
      + 125349873400091034433910854988526736119231322948 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 125349873400091034433910854988526736119231322948
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

theorem worldtrace_ray_mod_eight (u : Nat)
    (H : ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*((8:Nat):ℤ) - 27))) :
    u % M = 72414318613725182000182971030813176026502347727 := by
  obtain ⟨W, hW⟩ := worldtrace_ray_residue 8 u H
  have hMval : (M:ℤ) = 515377520732011331036461129765621272702107522001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (7:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ) * W := by
    linear_combination hW
  have hdec : (7:ℤ)*(INV:ℤ)
      = (515377520732011331036461129765621272702107522001:ℤ)*3
      + 72414318613725182000182971030813176026502347727 := by decide
  show u % 515377520732011331036461129765621272702107522001
      = 72414318613725182000182971030813176026502347727
  have hdm := Nat.div_add_mod u 515377520732011331036461129765621272702107522001
  omega

/-- **THE WORLDTRACE RAY FLOOR.**  Every three-free core on the
worldtrace ghost ray exceeds `rayMin ≈ 7.24 × 10^46` — unconditional,
kernel-certified at depth one hundred.  This is the Mahler seam's entire
below-`10^46` content, closed by computation. -/
theorem worldtrace_ray_floor (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hg : WTGhostRay u) :
    rayMin ≤ u := by
  have hgh : GSTGhostRay.GhostRay u := (wtghostray_iff_ghostray u).mp hg
  have hconv := worldtrace_ray_convergence u hu3 hgh
  have hlt : (c 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
  have hunit : ¬ 3 ∣ (c 1 * u) % 9 := by
    have hgu := GSTGhostRay.ghost_head_unit u hu3
    rwa [← monolith_c_eq_tower 1 (by omega)] at hgu
  have hA : (c 1 * u) % 9 = 1 ∨ (c 1 * u) % 9 = 2 ∨ (c 1 * u) % 9 = 4
    ∨ (c 1 * u) % 9 = 5 ∨ (c 1 * u) % 9 = 7 ∨ (c 1 * u) % 9 = 8 := by
    omega
  rcases hA with h1 | h2 | h4 | h5 | h7 | h8
  · rw [h1] at hconv
    have hres := worldtrace_ray_mod_one u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.1
    omega
  · rw [h2] at hconv
    have hres := worldtrace_ray_mod_two u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.2.1
    omega
  · rw [h4] at hconv
    have hres := worldtrace_ray_mod_four u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.2.2.1
    omega
  · rw [h5] at hconv
    have hres := worldtrace_ray_mod_five u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.2.2.2.1
    omega
  · rw [h7] at hconv
    have hres := worldtrace_ray_mod_seven u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.2.2.2.2.1
    omega
  · rw [h8] at hconv
    have hres := worldtrace_ray_mod_eight u hconv
    have hdm := Nat.div_add_mod u M
    have hmin := rayMin_le_residues.2.2.2.2.2
    omega

/-- **THE RAY IS EMPTY BELOW THE FLOOR.**  No three-free natural below
`rayMin ≈ 7.24 × 10^46` lies on the worldtrace ghost ray — no Mahler
input, no compression input, no hypotheses at all. -/
theorem worldtrace_ray_empty_below (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hlt : u < rayMin) :
    ¬ WTGhostRay u :=
  fun hg => absurd (worldtrace_ray_floor u hu3 hg) (by omega)

/-! ## §13 THE COMPRESSION-SIDE COROLLARY — the conjecture certified
below the floor under ONE hypothesis

Under the compression hypothesis ALONE (the Mahler input eliminated
below the floor by `worldtrace_ray_floor`), no Cantorian exponent
exists below `rayMin` — the 1979 conjecture is certified for every
exponent below `7.24 × 10^46` under a single named input. -/

/-- Under the compression alone, no Cantorian exponent exists below the
ray floor: any such `K = 3^s * u` has core `u ≤ K < rayMin`, which the
unconditional floor theorem kills. -/
theorem no_cantorian_below_ray_floor (HC : WorldtraceCompression) :
    ¬ ∃ K : Nat, 8 ≤ K ∧ K < rayMin
      ∧ GSTClimbInfiniteFamily.CantorianPower K := by
  rintro ⟨K, hK8, hKlt, hcp⟩
  obtain ⟨s, u, hsu, hu⟩ :=
    GSTGhostRay.exists_three_free_decomp K K (by omega) (by omega)
  have huK : u ≤ K := by
    rcases Nat.eq_zero_or_pos s with hs0 | hs0
    · rw [hsu, hs0, Nat.pow_zero, Nat.one_mul]
    · rw [hsu]
      exact Nat.le_mul_of_pos_left u (Nat.pow_pos (by decide))
  exact worldtrace_ray_empty_below u hu (by omega) (HC K s u hsu hu hK8 hcp)

/-- **THE CONJECTURE BELOW THE FLOOR, UNDER ONE HYPOTHESIS.**  Under the
compression input alone, every `4^K` with `8 ≤ K < rayMin` owns its
ternary digit two — the 1979 statement certified to `7.24 × 10^46`. -/
theorem erdos_ternary_below_ray_floor (HC : WorldtraceCompression)
    (K : Nat) (hK8 : 8 ≤ K) (hKlt : K < rayMin) :
    noTernaryTwo (4^K) = false := by
  have hnc : ¬ GSTClimbInfiniteFamily.CantorianPower K := by
    intro hcp
    exact absurd ⟨K, hK8, hKlt, hcp⟩ (no_cantorian_below_ray_floor HC)
  unfold GSTClimbInfiniteFamily.CantorianPower at hnc
  push_neg at hnc
  obtain ⟨p, _, hp⟩ := hnc
  exact has_two_imp_not_no_two (4^K)
    (hasTernaryTwo_of_digit (4^K) p
      (by simpa [GSTCanonicalSevenAxisBridge.digit3] using hp))

/-! ## §14 THE REFINED FUSION — the Mahler input restricted above the
floor

The fusion's conditional content shrinks: the act now closes under the
compression plus the Mahler lock restricted to cores `≥ rayMin` — the
entire below-`10^46` range of the Mahler seam is discharged
unconditionally by the floor theorem. -/

/-- **THE MAHLER LOCK ABOVE THE FLOOR.**  The rational-lock denial,
restricted to cores from `rayMin` upward — the exact residual seam after
the floor theorem's unconditional discharge of the below-range. -/
def WorldtraceMahlerLockAbove : Prop :=
  ¬ ∃ (a u : Nat), (a < 9 ∧ ¬ 3 ∣ a) ∧ (¬ 3 ∣ u) ∧ rayMin ≤ u ∧
    ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
      (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(a:ℤ) - 27))

/-- The full lock implies the restricted lock: the residual seam only
shrank. -/
theorem worldtrace_mahler_lock_above_of_lock
    (H : WorldtraceMahlerLock) : WorldtraceMahlerLockAbove := by
  rintro ⟨a, u, ha, hu3, _hmin, hconv⟩
  exact H ⟨a, u, ha, hu3, hconv⟩

/-- **THE REFINED FUSION.**  The compression plus the Mahler lock above
the floor close the act: any Cantorian exponent from eight on compresses
onto the ray, the floor theorem unconditionally kills every core below
`rayMin`, and the restricted lock kills the rest. -/
theorem the_act_of_worldtrace_fusion_refined
    (HA : WorldtraceMahlerLockAbove) (HC : WorldtraceCompression) :
    GSTTheAct.the_act := by
  have hnc : ¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K := by
    rintro ⟨K, hK, hcp⟩
    obtain ⟨s, u, hsu, hu⟩ :=
      GSTGhostRay.exists_three_free_decomp K K (by omega) (by omega)
    have hray : WTGhostRay u := HC K s u hsu hu hK hcp
    have hmin : rayMin ≤ u := worldtrace_ray_floor u hu hray
    have hgh : GSTGhostRay.GhostRay u := (wtghostray_iff_ghostray u).mp hray
    have hconv := worldtrace_ray_convergence u hu hgh
    have hlt : (c 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
    have hunit : ¬ 3 ∣ (c 1 * u) % 9 := by
      have hgu := GSTGhostRay.ghost_head_unit u hu
      rwa [← monolith_c_eq_tower 1 (by omega)] at hgu
    exact HA ⟨(c 1 * u) % 9, u, ⟨hlt, hunit⟩, hu, hmin, hconv⟩
  exact GSTTheAct.the_act_iff_hTailF.mpr
    (GSTClimbInfiniteFamily.hTailF_of_no_cantorian hnc)

/-! ## §15 THE RECEIPT -/

/-- **THE WORLDTRACE RAY FLOOR RECEIPT.**  Everything in one theorem:
the unconditional floor (every ray core exceeds `7.24 × 10^46`), the
unconditional emptiness below it, the compression-side corollary (the
conjecture certified below the floor under one hypothesis), and the
refined fusion (the act under the compression plus the Mahler lock
restricted above the floor). -/
theorem the_worldtrace_ray_floor_receipt :
    (∀ (u : Nat), ¬ 3 ∣ u → WTGhostRay u → rayMin ≤ u) ∧
    (∀ (u : Nat), ¬ 3 ∣ u → u < rayMin → ¬ WTGhostRay u) ∧
    (∀ (HC : WorldtraceCompression), ¬ ∃ K : Nat, 8 ≤ K ∧ K < rayMin
      ∧ GSTClimbInfiniteFamily.CantorianPower K) ∧
    (∀ (HC : WorldtraceCompression) (K : Nat), 8 ≤ K → K < rayMin →
      noTernaryTwo (4^K) = false) ∧
    (∀ (HA : WorldtraceMahlerLockAbove) (HC : WorldtraceCompression),
      GSTTheAct.the_act) ∧
    (∀ (H : WorldtraceMahlerLock), WorldtraceMahlerLockAbove) ∧
    (∀ (H : WorldtraceMahlerLock) (HC : WorldtraceCompression),
      ∀ n : Nat, noTernaryTwo (2^n) = true
        ↔ (n = 0 ∨ n = 2 ∨ n = 8)) :=
  ⟨worldtrace_ray_floor,
    worldtrace_ray_empty_below,
    no_cantorian_below_ray_floor,
    erdos_ternary_below_ray_floor,
    the_act_of_worldtrace_fusion_refined,
    worldtrace_mahler_lock_above_of_lock,
    fun H HC => erdos_ternary_classification H HC⟩

#print axioms c_mod_ninetynine
#print axioms worldtrace_ray_residue
#print axioms worldtrace_ray_floor
#print axioms worldtrace_ray_empty_below
#print axioms no_cantorian_below_ray_floor
#print axioms erdos_ternary_below_ray_floor
#print axioms the_act_of_worldtrace_fusion_refined
#print axioms the_worldtrace_ray_floor_receipt

end GSTWorldtraceFusion
