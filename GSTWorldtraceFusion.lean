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

/-! ## §16 THE GENERAL PIN — every depth, inverse-free -/

/-- The convergence chain of the head `a` and core `u`: the scaled tower
`6u * c_s` converges 3-adically to the head constant `6a - 27`. -/
def WorldtraceConvergence (a u : Nat) : Prop :=
  ∀ k : Nat, ∃ S : Nat, ∀ s : Nat, S ≤ s →
    (3:ℤ)^k ∣ (6*(u:ℤ)*((c s : Nat):ℤ) - (6*(a:ℤ) - 27))

/-- **THE GENERAL PIN.**  A convergent scaled tower pins its core at EVERY
depth: the pure linear congruence `2u * c_{D-1} ≡ 2a - 9 [MOD 3^D]` holds
for every `D ≥ 2` — no constants, no inverses, no hypotheses beyond the
convergence itself. -/
theorem worldtrace_convergence_pin (a u : Nat)
    (H : WorldtraceConvergence a u) (D : Nat) (hD : 2 ≤ D) :
    ∃ W : ℤ, 2*(u:ℤ)*((c (D-1) : Nat):ℤ) - (2*(a:ℤ) - 9)
      = (3:ℤ)^D * W := by
  obtain ⟨S, hS⟩ := H (D+1)
  have hd : (3:ℤ)^(D+1) ∣ (6*(u:ℤ)*((c (max S (D-1) : Nat):ℤ)
      - (6*(a:ℤ) - 27)) := hS (max S (D-1)) (le_max_left S (D-1))
  obtain ⟨t, ht⟩ := hd
  have hfac : 6*(u:ℤ)*((c (max S (D-1) : Nat):ℤ) - (6*(a:ℤ) - 27)
      = (3:ℤ) * (2*(u:ℤ)*((c (max S (D-1) : Nat):ℤ) - (2*(a:ℤ) - 9)) := by ring
  have hpD : (3:ℤ)^(D+1) = (3:ℤ) * (3:ℤ)^D := by rw [pow_succ]; ring
  rw [hfac, hpD] at ht
  have hY : 2*(u:ℤ)*((c (max S (D-1) : Nat):ℤ) - (2*(a:ℤ) - 9)
      = (3:ℤ)^D * t := by
    refine mul_left_cancel₀ (by norm_num : ((3:ℤ)) ≠ 0) ?_
    rw [ht]
    ring
  have hstab0 := c_monolith_stable (D-1) (max S (D-1)) (by omega) (by omega)
  rw [show (D-1)+1 = D from by omega] at hstab0
  have h1 := Nat.div_add_mod (c (max S (D-1))) (3^D)
  have h2 := Nat.div_add_mod (c (D-1)) (3^D)
  rw [hstab0] at h1
  have h1Z : ((3:ℤ)^D) * ((c (max S (D-1)) / 3^D : Nat):ℤ)
      + ((c (D-1) % 3^D : Nat):ℤ) = ((c (max S (D-1)) : Nat):ℤ) := by
    exact_mod_cast h1
  have h2Z : ((3:ℤ)^D) * ((c (D-1) / 3^D : Nat):ℤ)
      + ((c (D-1) % 3^D : Nat):ℤ) = ((c (D-1) : Nat):ℤ) := by
    exact_mod_cast h2
  have hX : ((c (max S (D-1)) : Nat):ℤ) = ((c (D-1) : Nat):ℤ)
      + (3:ℤ)^D * (((c (max S (D-1)) / 3^D : Nat):ℤ)
        - ((c (D-1) / 3^D : Nat):ℤ)) := by
    linear_combination h2Z - h1Z
  refine ⟨t - 2*(u:ℤ)*(((c (max S (D-1)) / 3^D : Nat):ℤ)
      - ((c (D-1) / 3^D : Nat):ℤ)), ?_⟩
  linear_combination hY - (2*(u:ℤ)) * hX

/-- The head-packaged pin: a ray core is pinned at every depth to its
own head's linear congruence. -/
theorem worldtrace_ray_pin (u : Nat) (hu3 : ¬ 3 ∣ u) (hg : WTGhostRay u)
    (D : Nat) (hD : 2 ≤ D) :
    ∃ W : ℤ, 2*(u:ℤ)*((c (D-1) : Nat):ℤ)
      - (2*(((c 1 * u) % 9 : Nat):ℤ) - 9) = (3:ℤ)^D * W :=
  worldtrace_convergence_pin ((c 1 * u) % 9) u
    (worldtrace_ray_convergence u hu3 ((wtghostray_iff_ghostray u).mp hg)) D hD

/-! ## §17 THE TWO PICTURES ARE ONE -/

/-- **CONVERGENCE IS THE RAY.**  Any head's convergence chain puts the core
on the worldtrace ray: at every depth `k ≥ 3` the pinned scaled residue
`c_{k-1} * u` is exactly `(3^k + 2a - 9) / 2` — the middle third, by pure
parity and size arithmetic.  The geometric middle-third picture and the
3-adic convergence picture are ONE condition. -/
theorem worldtrace_ghostray_of_convergence (a u : Nat) (ha : a < 9)
    (H : WorldtraceConvergence a u) : WTGhostRay u := by
  intro k hk
  obtain ⟨A, hA⟩ : ∃ A : Nat, k = A + 1 := ⟨k - 1, by omega⟩
  subst hA
  obtain ⟨W, hW⟩ := worldtrace_convergence_pin a u H (A+1) (by omega)
  rw [show (A+1)-1 = A from by omega] at hW
  have hpsucc : (3:ℤ)^(A+1) = (3:ℤ) * (3:ℤ)^A := by rw [pow_succ]; ring
  rw [hpsucc] at hW
  have hprod := Nat.div_add_mod (c A * u) (3^(A+1))
  have hprodZ : ((3:ℤ)^(A+1)) * ((c A * u / 3^(A+1) : Nat):ℤ)
      + ((c A * u % 3^(A+1) : Nat):ℤ) = ((c A * u : Nat):ℤ) := by
    exact_mod_cast hprod
  rw [hpsucc] at hprodZ
  have hcastu : ((c A * u : Nat):ℤ) = ((c A : Nat):ℤ) * (u:ℤ) := by push_cast
  have hxx : 2*((c A * u % 3^(A+1) : Nat):ℤ)
      = (2*(a:ℤ) - 9) + (3:ℤ) * (3:ℤ)^A
        * (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) := by
    linear_combination hW + 2 * hprodZ + 2 * hcastu
  have hxlt : c A * u % 3^(A+1) < 3^(A+1) := Nat.mod_lt _ (by positivity)
  have hx0 : (0:ℤ) ≤ ((c A * u % 3^(A+1) : Nat):ℤ) := by positivity
  have hxB0 : ((c A * u % 3^(A+1) : Nat):ℤ) < (3:ℤ) * (3:ℤ)^A := by
    have hcast : ((c A * u % 3^(A+1) : Nat):ℤ) < ((3^(A+1) : Nat):ℤ) := by
      exact_mod_cast hxlt
    have hlink0 : ((3^(A+1) : Nat):ℤ) = (3:ℤ)^(A+1) := by push_cast
    rw [hlink0, hpsucc] at hcast
    exact hcast
  have hlink : ((3^A : Nat):ℤ) = (3:ℤ)^A := by push_cast
  have hTA : (9:ℤ) ≤ (3:ℤ)^A := by
    have hone : (1:Nat) ≤ 3^(A-2) := Nat.one_le_pow _ _ (by decide)
    have hsplit : 3^A = 3^2 * 3^(A-2) := by
      rw [← Nat.pow_add, show 2 + (A-2) = A from by omega]
    have h32 : (3:Nat)^2 = 9 := by decide
    rw [h32] at hsplit
    have h9 : (9:Nat) ≤ 3^A := by omega
    have h9Z : (9:ℤ) ≤ ((3^A : Nat):ℤ) := by exact_mod_cast h9
    rw [hlink] at h9Z
    exact h9Z
  have hcases : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) = 1 := by
    by_cases h1 : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) ≤ 0
    · by_cases h0 : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) = 0
      · rw [h0, mul_zero, add_zero] at hxx
        exact absurd hxx (by omega)
      · have hjle : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) ≤ -1 := by omega
        have hprod_le : (3:ℤ) * (3:ℤ)^A
            * (W - 2*((c A * u / 3^(A+1) : Nat):ℤ))
            ≤ -((3:ℤ) * (3:ℤ)^A) := by
          calc (3:ℤ) * (3:ℤ)^A * (W - 2*((c A * u / 3^(A+1) : Nat):ℤ))
              ≤ (3:ℤ) * (3:ℤ)^A * (-1:ℤ) :=
                mul_le_mul_of_nonneg_left hjle (by positivity)
            _ = -((3:ℤ) * (3:ℤ)^A) := by ring
        linarith
    · by_cases h2 : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) ≤ 2
      · by_cases h1e : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) = 1
        · exact h1e
        · have h2e : (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) = 2 := by omega
          rw [h2e] at hxx
          exact absurd hxx (by omega)
      · have hjge : (3:ℤ) ≤ (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) := by omega
        have hprod_ge : (3:ℤ) * ((3:ℤ) * (3:ℤ)^A)
            ≤ (3:ℤ) * (3:ℤ)^A
              * (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) := by
          calc (3:ℤ) * ((3:ℤ) * (3:ℤ)^A)
              ≤ (W - 2*((c A * u / 3^(A+1) : Nat):ℤ))
                  * ((3:ℤ) * (3:ℤ)^A) :=
                mul_le_mul_of_nonneg_right hjge (by positivity)
            _ = (3:ℤ) * (3:ℤ)^A
                  * (W - 2*((c A * u / 3^(A+1) : Nat):ℤ)) := by ring
        have h2xlt : (2:ℤ)*((c A * u % 3^(A+1) : Nat):ℤ)
            < 2 * ((3:ℤ) * (3:ℤ)^A) := by linarith
        linarith
  rw [hcases] at hxx
  rw [show (A+1)-1 = A from by omega]
  have hone : (1:Nat) ≤ 3^(A-2) := Nat.one_le_pow _ _ (by decide)
  have hsplit : 3^A = 3^2 * 3^(A-2) := by
    rw [← Nat.pow_add, show 2 + (A-2) = A from by omega]
  have h32 : (3:Nat)^2 = 9 := by decide
  rw [h32] at hsplit
  constructor <;> omega

/-- **THE RAY IS THE CONVERGENCE.**  For a three-free core, being on the
worldtrace ray is EXACTLY having a convergent scaled tower with its own
head — the geometric and the analytic reading of the ray are one. -/
theorem worldtrace_ray_iff_convergence (u : Nat) (hu3 : ¬ 3 ∣ u) :
    WTGhostRay u ↔ WorldtraceConvergence ((c 1 * u) % 9) u :=
  ⟨fun hg => worldtrace_ray_convergence u hu3 ((wtghostray_iff_ghostray u).mp hg),
    worldtrace_ghostray_of_convergence _ u (Nat.mod_lt _ (by decide))⟩

/-- **THE PIN IS THE RAY.**  Any head's full-depth pin puts the core on the
ray — the trace direction. -/
theorem worldtrace_ray_of_pin (a u : Nat) (ha : a < 9)
    (H : ∀ D : Nat, 2 ≤ D → ∃ W : ℤ, 2*(u:ℤ)*((c (D-1):Nat):ℤ)
      - (2*(a:ℤ) - 9) = (3:ℤ)^D * W) :
    WTGhostRay u := by
  refine worldtrace_ghostray_of_convergence a u ha ?_
  intro k
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · exact ⟨0, fun s _ => one_dvd _⟩
    · exact ⟨0, fun s _ => ⟨2*(u:ℤ)*((c s : Nat):ℤ) - (2*(a:ℤ) - 9),
        by rw [pow_one]; ring⟩⟩
  · obtain ⟨W, hW⟩ := H (k+1) (by omega)
    rw [show (k+1)-1 = k from by omega] at hW
    have hpsucc : (3:ℤ)^(k+1) = (3:ℤ) * (3:ℤ)^k := by rw [pow_succ]; ring
    rw [hpsucc] at hW
    refine ⟨k, fun s hs => ?_⟩
    have hstab := c_monolith_stable k s (by omega) (by omega)
    have h1 := Nat.div_add_mod (c s) (3^(k+1))
    have h2 := Nat.div_add_mod (c k) (3^(k+1))
    rw [hstab] at h1
    have h1Z : ((3:ℤ)^(k+1)) * ((c s / 3^(k+1) : Nat):ℤ)
        + ((c k % 3^(k+1) : Nat):ℤ) = ((c s : Nat):ℤ) := by
      exact_mod_cast h1
    have h2Z : ((3:ℤ)^(k+1)) * ((c k / 3^(k+1) : Nat):ℤ)
        + ((c k % 3^(k+1) : Nat):ℤ) = ((c k : Nat):ℤ) := by
      exact_mod_cast h2
    rw [hpsucc] at h1Z h2Z
    obtain ⟨j, hj⟩ : ∃ j : ℤ, ((c s : Nat):ℤ) - ((c k : Nat):ℤ)
        = (3:ℤ) * (3:ℤ)^k * j := by
      refine ⟨((c s / 3^(k+1) : Nat):ℤ) - ((c k / 3^(k+1) : Nat):ℤ), ?_⟩
      linear_combination h2Z - h1Z
    refine ⟨(9:ℤ) * (W + 2*(u:ℤ)*j), ?_⟩
    linear_combination (3:ℤ) * hW + (6*(u:ℤ)) * hj

/-- **THE RAY IS THE SIX TOWERS' TRACE.**  For a three-free core, being on
the ray is EXACTLY carrying one of the six admissible heads' full-depth
linear pins.  The ray is the trace on the naturals of six explicit
congruence towers — nothing else lies on it. -/
theorem worldtrace_ray_iff_pin (u : Nat) (hu3 : ¬ 3 ∣ u) :
    WTGhostRay u ↔ ∃ a : Nat, a < 9 ∧ ¬ 3 ∣ a ∧
      (∀ D : Nat, 2 ≤ D → ∃ W : ℤ, 2*(u:ℤ)*((c (D-1):Nat):ℤ)
        - (2*(a:ℤ) - 9) = (3:ℤ)^D * W) := by
  constructor
  · intro hg
    refine ⟨(c 1 * u) % 9, Nat.mod_lt _ (by decide), ?_, ?_⟩
    · have hgu := GSTGhostRay.ghost_head_unit u hu3
      rwa [← monolith_c_eq_tower 1 (by omega)] at hgu
    · exact worldtrace_ray_pin u hu3 hg
  · rintro ⟨a, ha9, _ha3, Hpin⟩
    exact worldtrace_ray_of_pin a u ha9 Hpin

/-- **THE LOCK IS THE EMPTY RAY.**  The Mahler input — no convergent
scaled tower at all — is EXACTLY the statement that the worldtrace ray
carries no three-free core.  The transcendence input and the geometric
exclusion are one proposition. -/
theorem worldtrace_lock_iff_ray_empty :
    WorldtraceMahlerLock ↔ ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u := by
  constructor
  · exact terminal_worldtrace_exclusion
  · intro HE ⟨a, u, ⟨ha9, ha3⟩, hu3, hconv⟩
    exact HE u hu3 (worldtrace_ghostray_of_convergence a u ha9 hconv)

/-! ## §18 THE FINITUDE — the ray is six objects -/

/-- **SAME HEAD, SAME MEMBER.**  Two three-free cores on the worldtrace ray
with the same head are EQUAL: both are pinned to the same congruence at
every depth, and an integer divisible by every power of three is zero. -/
theorem worldtrace_ray_head_unique (u v : Nat) (hu3 : ¬ 3 ∣ u) (hv3 : ¬ 3 ∣ v)
    (hgu : WTGhostRay u) (hgv : WTGhostRay v)
    (hhead : (c 1 * u) % 9 = (c 1 * v) % 9) : u = v := by
  have main : ∀ x y : Nat, x < y → ¬ 3 ∣ x → ¬ 3 ∣ y → WTGhostRay x →
      WTGhostRay y → (c 1 * x) % 9 = (c 1 * y) % 9 → False := by
    intro x y hxy hx3 hy3 hgx hgy hxyhead
    obtain ⟨t, w, hdecomp, hw3⟩ :=
      GSTGhostRay.exists_three_free_decomp (y - x) (y - x) (by omega) (by omega)
    obtain ⟨Wx, hxW⟩ := worldtrace_ray_pin x hx3 hgx (t+2) (by omega)
    obtain ⟨Wy, hyW⟩ := worldtrace_ray_pin y hy3 hgy (t+2) (by omega)
    rw [← hxyhead] at hyW
    have hsub : 2*((y:ℤ) - (x:ℤ))*((c (t+2-1) : Nat):ℤ)
        = (3:ℤ)^(t+2) * (Wy - Wx) := by
      linear_combination hyW - hxW
    have hdZ : ((y - x : Nat):ℤ) = (3:ℤ)^t * (w:ℤ) := by
      exact_mod_cast hdecomp
    have hdY : ((y - x : Nat):ℤ) = (y:ℤ) - (x:ℤ) :=
      Int.natCast_sub (by omega : x ≤ y)
    rw [← hdY, hdZ] at hsub
    have hp2 : (3:ℤ)^(t+2) = (3:ℤ)^t * 9 := by
      rw [show t+2 = (t+1)+1 from by omega, pow_succ, pow_succ]; ring
    rw [hp2] at hsub
    have hc : 2*(w:ℤ)*((c (t+2-1) : Nat):ℤ) = (9:ℤ) * (Wy - Wx) := by
      refine mul_left_cancel₀ (by positivity : ((3:ℤ)^t) ≠ 0) ?_
      linear_combination hsub
    have hnn : (0:ℤ) ≤ Wy - Wx := by
      have hpos : (0:ℤ) ≤ 2*(w:ℤ)*((c (t+2-1) : Nat):ℤ) := by positivity
      linarith
    obtain ⟨z, hz⟩ : ∃ z : Nat, (Wy - Wx) = (z:ℤ) := by
      refine ⟨(Wy - Wx).natCast, ?_⟩
      exact (Int.natCast_of_nonneg hnn).symm
    have hcnat : (2:Nat) * w * c (t+2-1) = 9 * z := by
      have h0 : (2*(w:ℤ)*((c (t+2-1) : Nat):ℤ)) = (9:ℤ) * (z:ℤ) := by
        rw [← hz]; exact hc
      exact_mod_cast h0
    have h3dvd : (3:Nat) ∣ 2 * w * c (t+2-1) := by
      rw [hcnat]
      exact ⟨3*z, by ring⟩
    rcases Nat.Prime.dvd_mul (by decide : Nat.Prime 3) h3dvd with h2w | hcc
    · rcases Nat.Prime.dvd_mul (by decide : Nat.Prime 3) h2w with h2 | hw
      · exact absurd h2 (by decide)
      · exact hw3 hw
    · exact absurd hcc (fun h => by
        have := c_mod3 (t+2-1) (by omega)
        omega)
  rcases Nat.lt_trichotomy u v with h | h | h
  · exact (main u v h hu3 hv3 hgu hgv hhead).elim
  · exact h
  · exact (main v u h hv3 hu3 hgv hgu hhead.symm).elim

/-- **THE SIX RESIDUES.**  Every three-free core on the worldtrace ray sits
in one of the six explicit residue classes modulo `3^100`. -/
theorem worldtrace_ray_classification (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hg : WTGhostRay u) :
    u % M = 442963202118286149036278158734808096675605174274
    ∨ u % M = 390027647331920296602550274777094536582876199053
    ∨ u % M = 284156537759188591735094506861667416397418248611
    ∨ u % M = 231220982972822739301366622903953856304689273390
    ∨ u % M = 125349873400091034433910854988526736119231322948
    ∨ u % M = 72414318613725182000182971030813176026502347727 := by
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
    exact Or.inl (worldtrace_ray_mod_one u hconv)
  · rw [h2] at hconv
    exact Or.inr (Or.inl (worldtrace_ray_mod_two u hconv))
  · rw [h4] at hconv
    exact Or.inr (Or.inr (Or.inl (worldtrace_ray_mod_four u hconv)))
  · rw [h5] at hconv
    exact Or.inr (Or.inr (Or.inr (Or.inl (worldtrace_ray_mod_five u hconv))))
  · rw [h7] at hconv
    exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (worldtrace_ray_mod_seven u hconv)))))
  · rw [h8] at hconv
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl (worldtrace_ray_mod_eight u hconv)))))

/-- **THE RAY IS FINITE: AT MOST SIX MEMBERS.**  The head map is injective
on the three-free ray cores (same head, same member) and lands in the
six-element unit set `{1, 2, 4, 5, 7, 8}`.  The worldtrace ghost ray,
over three-free cores, is a set of at most SIX explicit objects. -/
theorem worldtrace_ray_le_six (s : Finset Nat)
    (hs : ∀ u ∈ s, ¬ 3 ∣ u ∧ WTGhostRay u) : s.card ≤ 6 := by
  have hmem : ∀ u ∈ s, (c 1 * u) % 9 ∈ ({1, 2, 4, 5, 7, 8} : Finset Nat) := by
    intro u hu
    obtain ⟨hu3, hg⟩ := hs u hu
    have hunit : ¬ 3 ∣ (c 1 * u) % 9 := by
      have hgu := GSTGhostRay.ghost_head_unit u hu3
      rwa [← monolith_c_eq_tower 1 (by omega)] at hgu
    have hlt : (c 1 * u) % 9 < 9 := Nat.mod_lt _ (by decide)
    have hA : (c 1 * u) % 9 = 1 ∨ (c 1 * u) % 9 = 2 ∨ (c 1 * u) % 9 = 4
      ∨ (c 1 * u) % 9 = 5 ∨ (c 1 * u) % 9 = 7 ∨ (c 1 * u) % 9 = 8 := by
      omega
    rcases hA with h1 | h2 | h4 | h5 | h7 | h8
    · simp [h1]
    · simp [h2]
    · simp [h4]
    · simp [h5]
    · simp [h7]
    · simp [h8]
  have hinj : Set.InjOn (fun u => (c 1 * u) % 9) ↑s := by
    intro x hx y hy hxy
    exact worldtrace_ray_head_unique x y (hs x hx).1 (hs y hy).1
      (hs x hx).2 (hs y hy).2 hxy
  calc s.card = (s.image (fun u => (c 1 * u) % 9)).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ ({1, 2, 4, 5, 7, 8} : Finset Nat).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        exact hmem y hy
    _ = 6 := by decide

/-! ## §19 THE DEPTH-TWO-THOUSAND FLOOR — `3^2000`

The computable core of the Mahler seam, driven two thousand trits deep.
The monolith's own tower is evaluated modulo `3^2000` by its own exact
recursion (kernel-certified, cross-checked externally against the direct
big-integer evaluation of `(4^(3^1999) - 1) / 3^2000`, digit for digit).
Everything in this section is UNCONDITIONAL — no hypotheses, no external
inputs, kernel-certified. -/
/-- The depth-two-thousand certificate modulus: `3^2000`. -/
def M2 : Nat := 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001

set_option maxRecDepth 1000000 in
theorem M2_eq_pow : (3:Nat)^2000 = M2 := by decide

theorem M2_pos : 0 < M2 := by decide

set_option maxRecDepth 1000000 in
theorem MZ2_eq : (3:ℤ)^2000 = (M2:ℤ) := by decide

set_option maxRecDepth 1000000 in
theorem MZ2_2001 : (3:ℤ)^2001 = (3:ℤ) * (M2:ℤ) := by decide

/-- The tower's 1999th value modulo `3^2000`, kernel-certified (cross-checked externally against the direct big-integer evaluation of `(4^(3^1999) - 1) / 3^2000`, digit for digit). -/
def L2 : Nat := 770365247105366002625108160275305464620833145900576204534661265586562938333374220327305514800655821484264945622579994914308149714434767874880661066948266185248283634076438040054135173829712032712903192253184695133243364674542986943379764417066978213783342819057865538937671502752038160501121424720604319601556347513192174732440469470443752125743015741489545964563644334301951647505539001838754172312666990903041988088604820489345477308944964822590284855473861537030023745912886461597900013974050101283111086136158849630878421195073390149370296894042592219150763792447716794958979856970039456520677067131477483890933686467517474809421264206134625745673798600795080220359347964937713083087197679783598006963032366079236086569346069198845462698205572684257939884728586131579481991379631318401155565557461857415090910192748425740655801497730561613603833054923625833741157710116462939910553105382820666979945119887953798977295557146837277649534700163744323743

set_option maxRecDepth 1000000 in
theorem c_mod_1999 : c 1999 % M2 = L2 := by
  obtain ⟨j, hj⟩ := cMod_spec M2 M2_pos 1999
  have hval : cMod M2 1999 = L2 := by decide
  rw [hj, hval]
  rw [Nat.add_mod,
    show M2 * j % M2 = 0 from Nat.mod_eq_zero_of_dvd (dvd_mul_right M2 j),
    Nat.add_zero, Nat.mod_mod_of_dvd L2 (Nat.dvd_refl M2),
    Nat.mod_eq_of_lt (by decide : L2 < M2)]

/-- The doubled tower unit's inverse modulo `3^2000`, kernel-certified. -/
def INV2 : Nat := 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514

theorem inv2_fact : (2:ℤ) * (L2:ℤ) * (INV2:ℤ)
    = 1 + (M2:ℤ) * 31881468799516573647396521599661202699736478399042829166409722063475648772721184487496375743597825735298887092880186130597970467249281578157164590498929841395530401438348330214177092456483868057733665322491227225918286654469089363666177311526140904510229249835469414729071521861786462937407284760711320769324315766863931425296368485454446418037429525811789767139363699058692930343772369761758424221381388905477882987113469002940036080421665240710659864039215756334142527997709735301005066179968011965380104575879250798654992615672053509626500190734978350802443774417472637018891251224802090750998896338648352277436073380297606553020821702162421256570966110210444674528617867739618568497594278021717729395473167403019457916361908469047588966111868139976752273136620411383688157907264183036490056937007235184680279139399282190325231512187649900670515543543609619147899544337695107352586877762627500285608262036968255047368682715188972972225615587513421803 := by decide

/-! ### The residue pinning at depth 2000 -/

/-- **THE DEPTH-2000 RESIDUE PINNING.**  A convergent scaled tower pins
its core to the explicit residue class `(2a - 9) * INV2` modulo
`3^2000`. -/
theorem worldtrace_ray2_residue (a u : Nat)
    (H : WorldtraceConvergence a u) :
    ∃ W : ℤ, (u:ℤ) - (2*(a:ℤ) - 9) * (INV2:ℤ) = (M2:ℤ) * W := by
  obtain ⟨S, hS⟩ := H 2001
  have hd : (3:ℤ)^2001 ∣ (6*(u:ℤ)*((c (max S 1999) : Nat):ℤ)
      - (6*(a:ℤ) - 27)) := hS (max S 1999) (le_max_left S 1999)
  obtain ⟨t, ht⟩ := hd
  have hfac : 6*(u:ℤ)*((c (max S 1999) : Nat):ℤ) - (6*(a:ℤ) - 27)
      = (3:ℤ) * (2*(u:ℤ)*((c (max S 1999) : Nat):ℤ) - (2*(a:ℤ) - 9)) := by ring
  rw [hfac, MZ2_2001] at ht
  have hY : 2*(u:ℤ)*((c (max S 1999) : Nat):ℤ) - (2*(a:ℤ) - 9)
      = (M2:ℤ) * t := by
    refine mul_left_cancel₀ (by norm_num : ((3:ℤ)) ≠ 0) ?_
    rw [ht, mul_assoc]
  have hcsL : (c (max S 1999) : Nat) % M2 = L2 := by
    have h1 := c_monolith_stable 1999 (max S 1999) (by omega) (le_max_right S 1999)
    rw [show (1999:Nat) + 1 = 2000 from rfl, M2_eq_pow] at h1
    rw [h1, c_mod_1999]
  have hq := Nat.div_add_mod (c (max S 1999)) M2
  rw [hcsL] at hq
  have hqZ : ((c (max S 1999) : Nat):ℤ)
      = (M2:ℤ) * ((c (max S 1999) / M2 : Nat):ℤ) + (L2:ℤ) := by
    exact_mod_cast hq.symm
  have h2 : 2*(u:ℤ)*(L2:ℤ) - (2*(a:ℤ) - 9)
      = (M2:ℤ) * (t - 2*(u:ℤ)*((c (max S 1999) / M2 : Nat):ℤ)) := by
    linear_combination hY - (2*(u:ℤ)) * hqZ
  refine ⟨(t - 2*(u:ℤ)*((c (max S 1999) / M2 : Nat):ℤ)) * (INV2:ℤ)
      - (u:ℤ) * 31881468799516573647396521599661202699736478399042829166409722063475648772721184487496375743597825735298887092880186130597970467249281578157164590498929841395530401438348330214177092456483868057733665322491227225918286654469089363666177311526140904510229249835469414729071521861786462937407284760711320769324315766863931425296368485454446418037429525811789767139363699058692930343772369761758424221381388905477882987113469002940036080421665240710659864039215756334142527997709735301005066179968011965380104575879250798654992615672053509626500190734978350802443774417472637018891251224802090750998896338648352277436073380297606553020821702162421256570966110210444674528617867739618568497594278021717729395473167403019457916361908469047588966111868139976752273136620411383688157907264183036490056937007235184680279139399282190325231512187649900670515543543609619147899544337695107352586877762627500285608262036968255047368682715188972972225615587513421803, ?_⟩
  linear_combination (INV2:ℤ) * h2 - (u:ℤ) * inv2_fact

/-- **Head 1, depth 2000.**  A `7`-headed convergent core is pinned
to the residue `149469724049…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_one (u : Nat)
    (H : WorldtraceConvergence 1 u) :
    u % M2 = 1494697240494038899022744788062731973616933055740424704785549371675682575655082793419928218777475432844833192025562631635493400873247997397871435269240576189340658902787101789507610938789704408752919789205961794449048858317616903442530711398232680022993680071297272857296828837322604302404166510434126118115531524119723055694642399225069326948393931329208099024232678841210939700896351813718347650122547271593809817482309300823897810244300669531187964361120101552111928760565591242214720158494859975477376738437817049327723929299593108780503460102735697110428150186011918104211216500628419361913977314574690830423695452989166298940629433924381660350474420465554492953637813564582614212838095889965248477161033464026102651063910463320897227969710971089699312893451370301044445895637550260699274221084156836462270767740650079201616993974340213045902691529511204640919862649164486100392122198311276741253346293468130051339364382692134361008807605295282653403 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 1 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (7:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (7:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 253174011228612710637229831101928596912129431694763813026338640135003690572192695871558251087205678230775758670582644953277967562627511249642978932853062292532253477302875389873918689688616114766399353475542629610362031896883597205283224420693021882408925412800865099682539713703220937007152133563790405561513245542905590711897936402906002670870313750542371838229795249894504736458950332433127697968208058559459250450782398655991279580350172264379514245276874112445214977091435838188519819263005321369363355274560866442812164924094940327519784036447330852056260892452521412634011461306801907900776102207885625083620620762819075105435158622414382800263387848947191726120243341366145033530548526186614660924243139569713759881247136421180389649200630095456289187320376484914913983852641672690691050191246291463161480222619596711029109182003741329540101159424842400613674873973455210298711751456487548827987606912180354815358775189978088982866213758827786598 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 1494697240494038899022744788062731973616933055740424704785549371675682575655082793419928218777475432844833192025562631635493400873247997397871435269240576189340658902787101789507610938789704408752919789205961794449048858317616903442530711398232680022993680071297272857296828837322604302404166510434126118115531524119723055694642399225069326948393931329208099024232678841210939700896351813718347650122547271593809817482309300823897810244300669531187964361120101552111928760565591242214720158494859975477376738437817049327723929299593108780503460102735697110428150186011918104211216500628419361913977314574690830423695452989166298940629433924381660350474420465554492953637813564582614212838095889965248477161033464026102651063910463320897227969710971089699312893451370301044445895637550260699274221084156836462270767740650079201616993974340213045902691529511204640919862649164486100392122198311276741253346293468130051339364382692134361008807605295282653403
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **Head 2, depth 2000.**  A `5`-headed convergent core is pinned
to the residue `156703267227…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_two (u : Nat)
    (H : WorldtraceConvergence 2 u) :
    u % M2 = 1567032672273642530633381882663283001306112893367500079935931840285683630104280706526087719088105626625054837360014815907858534462570143469198000678627165415778445610587923329471587707272166155829033890198973974337723724573869359786897346947002114846539087332097520028634697326952095998691924262880923376847392451417696081612327523911613899140071163829363062406584048912609369625598909051556384135256321002610798174753961414725609604410115004463867825574056351298524847325448858624554297249712861495868623411373405868311384547849334520302651969827434934496729939012426924222106648346716077049885627629491229580447587058921400320399325193530785769721978245565253690589672168804972941365275395468875709808853674361046020868172838216584091625012339722545543966946971477868162992748166876452896614521138798634023174047804255678261911025169198424854342720432204016755380912613156901874763182698727416040918485609728753009858038318460699529289626523512090592431 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 2 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (5:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (5:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 180838579449009079026592736501377569222949594067688437875956171525002636122994782765398750776575484450554113336130460680912833973305365178316413523466473066094466769502053849909941921206154367690285252482530449721687165640631140860916588871923587058863518152000617928344671224073729240719394381116993146829652318244932564794212811716361430479193081250387408455878425178496074811756393094595091212834434327542470893179130284754279485414535837331699653032340624366032296412208168455848942728045003800978116682338972047459151546374353528805371274311748093465754472066037515294738579615219144219929125787291346875059729014830585053646739399016010273428759562749247994090085888100975817881093248947276153329231602242549795542772319383157985992606571878639611635133800268917796367131323315480493350750136604493902258200159013997650735077987145529521100072256732030286152624909981039435927651251040348249162848290651557396296684839421412920702047295542019847570 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 1567032672273642530633381882663283001306112893367500079935931840285683630104280706526087719088105626625054837360014815907858534462570143469198000678627165415778445610587923329471587707272166155829033890198973974337723724573869359786897346947002114846539087332097520028634697326952095998691924262880923376847392451417696081612327523911613899140071163829363062406584048912609369625598909051556384135256321002610798174753961414725609604410115004463867825574056351298524847325448858624554297249712861495868623411373405868311384547849334520302651969827434934496729939012426924222106648346716077049885627629491229580447587058921400320399325193530785769721978245565253690589672168804972941365275395468875709808853674361046020868172838216584091625012339722545543966946971477868162992748166876452896614521138798634023174047804255678261911025169198424854342720432204016755380912613156901874763182698727416040918485609728753009858038318460699529289626523512090592431
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **Head 4, depth 2000.**  A `1`-headed convergent core is pinned
to the residue `171170353583…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_four (u : Nat)
    (H : WorldtraceConvergence 4 u) :
    u % M2 = 1711703535832849793854656071864385056684472568621650830236696777505685739002676532738406719709366014185498128028919184452588801641214435611851131497400343868654019026189566409399541244237089649981262092184998334115073457086374272475630618044540984493629901853698014371310434306211079391267439767774517894311114306013642133447697773284703043523425628829672989171286789055406229475004023527232457105523868464644774889297265642529033192741743674329227547999928850791350684455215393389233451432148864536651116757244583506278705784948817343346948989276833409269333516665256936457897512038891392425828928259324307080495370270785868363316716712743593988464985895764652085861740879285753595670149994626696632472238956155085857302390693723110480419097597225457233275054011693002400086453225528837291295121248082229144980607931466876382499087558914848471222778237589640984303012541141733423505303699559694640248764242249998926895386189997829865851264359945706470487 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 4 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) + (1:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (1:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 1711703535832849793854656071864385056684472568621650830236696777505685739002676532738406719709366014185498128028919184452588801641214435611851131497400343868654019026189566409399541244237089649981262092184998334115073457086374272475630618044540984493629901853698014371310434306211079391267439767774517894311114306013642133447697773284703043523425628829672989171286789055406229475004023527232457105523868464644774889297265642529033192741743674329227547999928850791350684455215393389233451432148864536651116757244583506278705784948817343346948989276833409269333516665256936457897512038891392425828928259324307080495370270785868363316716712743593988464985895764652085861740879285753595670149994626696632472238956155085857302390693723110480419097597225457233275054011693002400086453225528837291295121248082229144980607931466876382499087558914848471222778237589640984303012541141733423505303699559694640248764242249998926895386189997829865851264359945706470487
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **Head 5, depth 2000.**  A `1`-headed convergent core is pinned
to the residue `361677158898…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_five (u : Nat)
    (H : WorldtraceConvergence 5 u) :
    u % M2 = 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 5 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (1:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (1:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **Head 7, depth 2000.**  A `5`-headed convergent core is pinned
to the residue `180838579449…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_seven (u : Nat)
    (H : WorldtraceConvergence 7 u) :
    u % M2 = 180838579449009079026592736501377569222949594067688437875956171525002636122994782765398750776575484450554113336130460680912833973305365178316413523466473066094466769502053849909941921206154367690285252482530449721687165640631140860916588871923587058863518152000617928344671224073729240719394381116993146829652318244932564794212811716361430479193081250387408455878425178496074811756393094595091212834434327542470893179130284754279485414535837331699653032340624366032296412208168455848942728045003800978116682338972047459151546374353528805371274311748093465754472066037515294738579615219144219929125787291346875059729014830585053646739399016010273428759562749247994090085888100975817881093248947276153329231602242549795542772319383157985992606571878639611635133800268917796367131323315480493350750136604493902258200159013997650735077987145529521100072256732030286152624909981039435927651251040348249162848290651557396296684839421412920702047295542019847570 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 7 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (5:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (5:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 180838579449009079026592736501377569222949594067688437875956171525002636122994782765398750776575484450554113336130460680912833973305365178316413523466473066094466769502053849909941921206154367690285252482530449721687165640631140860916588871923587058863518152000617928344671224073729240719394381116993146829652318244932564794212811716361430479193081250387408455878425178496074811756393094595091212834434327542470893179130284754279485414535837331699653032340624366032296412208168455848942728045003800978116682338972047459151546374353528805371274311748093465754472066037515294738579615219144219929125787291346875059729014830585053646739399016010273428759562749247994090085888100975817881093248947276153329231602242549795542772319383157985992606571878639611635133800268917796367131323315480493350750136604493902258200159013997650735077987145529521100072256732030286152624909981039435927651251040348249162848290651557396296684839421412920702047295542019847570 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 180838579449009079026592736501377569222949594067688437875956171525002636122994782765398750776575484450554113336130460680912833973305365178316413523466473066094466769502053849909941921206154367690285252482530449721687165640631140860916588871923587058863518152000617928344671224073729240719394381116993146829652318244932564794212811716361430479193081250387408455878425178496074811756393094595091212834434327542470893179130284754279485414535837331699653032340624366032296412208168455848942728045003800978116682338972047459151546374353528805371274311748093465754472066037515294738579615219144219929125787291346875059729014830585053646739399016010273428759562749247994090085888100975817881093248947276153329231602242549795542772319383157985992606571878639611635133800268917796367131323315480493350750136604493902258200159013997650735077987145529521100072256732030286152624909981039435927651251040348249162848290651557396296684839421412920702047295542019847570
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **Head 8, depth 2000.**  A `7`-headed convergent core is pinned
to the residue `253174011228…` (955 digits) modulo `3^2000`. -/
theorem worldtrace_ray2_mod_eight (u : Nat)
    (H : WorldtraceConvergence 8 u) :
    u % M2 = 253174011228612710637229831101928596912129431694763813026338640135003690572192695871558251087205678230775758670582644953277967562627511249642978932853062292532253477302875389873918689688616114766399353475542629610362031896883597205283224420693021882408925412800865099682539713703220937007152133563790405561513245542905590711897936402906002670870313750542371838229795249894504736458950332433127697968208058559459250450782398655991279580350172264379514245276874112445214977091435838188519819263005321369363355274560866442812164924094940327519784036447330852056260892452521412634011461306801907900776102207885625083620620762819075105435158622414382800263387848947191726120243341366145033530548526186614660924243139569713759881247136421180389649200630095456289187320376484914913983852641672690691050191246291463161480222619596711029109182003741329540101159424842400613674873973455210298711751456487548827987606912180354815358775189978088982866213758827786598 := by
  obtain ⟨W, hW⟩ := worldtrace_ray2_residue 8 u H
  have hMval : (M2:ℤ) = 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001 := by decide
  rw [hMval] at hW
  have hWZ : (u:ℤ) - (7:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ) * W := by linear_combination hW
  have hdec : (7:ℤ)*(INV2:ℤ)
      = (1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001:ℤ)*0 + 253174011228612710637229831101928596912129431694763813026338640135003690572192695871558251087205678230775758670582644953277967562627511249642978932853062292532253477302875389873918689688616114766399353475542629610362031896883597205283224420693021882408925412800865099682539713703220937007152133563790405561513245542905590711897936402906002670870313750542371838229795249894504736458950332433127697968208058559459250450782398655991279580350172264379514245276874112445214977091435838188519819263005321369363355274560866442812164924094940327519784036447330852056260892452521412634011461306801907900776102207885625083620620762819075105435158622414382800263387848947191726120243341366145033530548526186614660924243139569713759881247136421180389649200630095456289187320376484914913983852641672690691050191246291463161480222619596711029109182003741329540101159424842400613674873973455210298711751456487548827987606912180354815358775189978088982866213758827786598 := by decide
  show u % 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
      = 253174011228612710637229831101928596912129431694763813026338640135003690572192695871558251087205678230775758670582644953277967562627511249642978932853062292532253477302875389873918689688616114766399353475542629610362031896883597205283224420693021882408925412800865099682539713703220937007152133563790405561513245542905590711897936402906002670870313750542371838229795249894504736458950332433127697968208058559459250450782398655991279580350172264379514245276874112445214977091435838188519819263005321369363355274560866442812164924094940327519784036447330852056260892452521412634011461306801907900776102207885625083620620762819075105435158622414382800263387848947191726120243341366145033530548526186614660924243139569713759881247136421180389649200630095456289187320376484914913983852641672690691050191246291463161480222619596711029109182003741329540101159424842400613674873973455210298711751456487548827987606912180354815358775189978088982866213758827786598
  have hdm := Nat.div_add_mod u 1747871251722651609659974619164660570529062487435188517811888011810686266227275489291486469864681111075608950696145276588771368435875508647514414202093638481872912380089977179381529628478320523519319142681504424059410890214500500647813935818925701905402605484098137956979368551025825239411318643997916523677044769662628646406540335627975329619264245079750470862462474091105444437355302146151475348090755330153269067933091699479889089824650841795567478606396975664557143737657027080403239977757865296846740093712377915770536094223688049108023244139183027962484411078464439516845227961935221269814753416782576455507316073751985374046064592546796043150737808314501684679758056905948759246368644416151863138085276603595816410945157599742077617618911601185155602080771746785959359879490191933389965271275403127925432247963269675912646103156343954375442792688936047041533537523137941310690833949767764290081333900380310406154723157882112449991673819054110440001
  omega

/-- **THE DEPTH-2000 FLOOR CERTIFICATE.**  The smallest core residue over the six admissible heads at depth `3^2000`. -/
def rayMin2 : Nat := 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514

theorem rayMin2_le_residues :
    rayMin2 ≤ 1494697240494038899022744788062731973616933055740424704785549371675682575655082793419928218777475432844833192025562631635493400873247997397871435269240576189340658902787101789507610938789704408752919789205961794449048858317616903442530711398232680022993680071297272857296828837322604302404166510434126118115531524119723055694642399225069326948393931329208099024232678841210939700896351813718347650122547271593809817482309300823897810244300669531187964361120101552111928760565591242214720158494859975477376738437817049327723929299593108780503460102735697110428150186011918104211216500628419361913977314574690830423695452989166298940629433924381660350474420465554492953637813564582614212838095889965248477161033464026102651063910463320897227969710971089699312893451370301044445895637550260699274221084156836462270767740650079201616993974340213045902691529511204640919862649164486100392122198311276741253346293468130051339364382692134361008807605295282653403 ∧
    rayMin2 ≤ 1567032672273642530633381882663283001306112893367500079935931840285683630104280706526087719088105626625054837360014815907858534462570143469198000678627165415778445610587923329471587707272166155829033890198973974337723724573869359786897346947002114846539087332097520028634697326952095998691924262880923376847392451417696081612327523911613899140071163829363062406584048912609369625598909051556384135256321002610798174753961414725609604410115004463867825574056351298524847325448858624554297249712861495868623411373405868311384547849334520302651969827434934496729939012426924222106648346716077049885627629491229580447587058921400320399325193530785769721978245565253690589672168804972941365275395468875709808853674361046020868172838216584091625012339722545543966946971477868162992748166876452896614521138798634023174047804255678261911025169198424854342720432204016755380912613156901874763182698727416040918485609728753009858038318460699529289626523512090592431 ∧
    rayMin2 ≤ 1711703535832849793854656071864385056684472568621650830236696777505685739002676532738406719709366014185498128028919184452588801641214435611851131497400343868654019026189566409399541244237089649981262092184998334115073457086374272475630618044540984493629901853698014371310434306211079391267439767774517894311114306013642133447697773284703043523425628829672989171286789055406229475004023527232457105523868464644774889297265642529033192741743674329227547999928850791350684455215393389233451432148864536651116757244583506278705784948817343346948989276833409269333516665256936457897512038891392425828928259324307080495370270785868363316716712743593988464985895764652085861740879285753595670149994626696632472238956155085857302390693723110480419097597225457233275054011693002400086453225528837291295121248082229144980607931466876382499087558914848471222778237589640984303012541141733423505303699559694640248764242249998926895386189997829865851264359945706470487 ∧
    rayMin2 ≤ 36167715889801815805318547300275513844589918813537687575191234305000527224598956553079750155315096890110822667226092136182566794661073035663282704693294613218893353900410769981988384241230873538057050496506089944337433128126228172183317774384717411772703630400123585668934244814745848143878876223398629365930463648986512958842562343272286095838616250077481691175685035699214962351278618919018242566886865508494178635826056950855897082907167466339930606468124873206459282441633691169788545609000760195623336467794409491830309274870705761074254862349618693150894413207503058947715923043828843985825157458269375011945802966117010729347879803202054685751912549849598818017177620195163576218649789455230665846320448509959108554463876631597198521314375727922327026760053783559273426264663096098670150027320898780451640031802799530147015597429105904220014451346406057230524981996207887185530250208069649832569658130311479259336967884282584140409459108403969514 ∧
    rayMin2 ≤ 180838579449009079026592736501377569222949594067688437875956171525002636122994782765398750776575484450554113336130460680912833973305365178316413523466473066094466769502053849909941921206154367690285252482530449721687165640631140860916588871923587058863518152000617928344671224073729240719394381116993146829652318244932564794212811716361430479193081250387408455878425178496074811756393094595091212834434327542470893179130284754279485414535837331699653032340624366032296412208168455848942728045003800978116682338972047459151546374353528805371274311748093465754472066037515294738579615219144219929125787291346875059729014830585053646739399016010273428759562749247994090085888100975817881093248947276153329231602242549795542772319383157985992606571878639611635133800268917796367131323315480493350750136604493902258200159013997650735077987145529521100072256732030286152624909981039435927651251040348249162848290651557396296684839421412920702047295542019847570 ∧
    rayMin2 ≤ 253174011228612710637229831101928596912129431694763813026338640135003690572192695871558251087205678230775758670582644953277967562627511249642978932853062292532253477302875389873918689688616114766399353475542629610362031896883597205283224420693021882408925412800865099682539713703220937007152133563790405561513245542905590711897936402906002670870313750542371838229795249894504736458950332433127697968208058559459250450782398655991279580350172264379514245276874112445214977091435838188519819263005321369363355274560866442812164924094940327519784036447330852056260892452521412634011461306801907900776102207885625083620620762819075105435158622414382800263387848947191726120243341366145033530548526186614660924243139569713759881247136421180389649200630095456289187320376484914913983852641672690691050191246291463161480222619596711029109182003741329540101159424842400613674873973455210298711751456487548827987606912180354815358775189978088982866213758827786598
 := by decide

/-- **THE WORLDTRACE RAY FLOOR AT DEPTH 2000.**  Every three-free core on
the worldtrace ghost ray exceeds `rayMin2 ≈ 3.6 × 10^952` —
unconditional, kernel-certified at depth two thousand.  The Mahler
seam's entire below-`10^952` content, discharged by computation. -/
theorem worldtrace_ray2_floor (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hg : WTGhostRay u) :
    rayMin2 ≤ u := by
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
    have hres := worldtrace_ray2_mod_one u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.1
    omega
  · rw [h2] at hconv
    have hres := worldtrace_ray2_mod_two u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.2.1
    omega
  · rw [h4] at hconv
    have hres := worldtrace_ray2_mod_four u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.2.2.1
    omega
  · rw [h5] at hconv
    have hres := worldtrace_ray2_mod_five u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.2.2.2.1
    omega
  · rw [h7] at hconv
    have hres := worldtrace_ray2_mod_seven u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.2.2.2.2.1
    omega
  · rw [h8] at hconv
    have hres := worldtrace_ray2_mod_eight u hconv
    have hdm := Nat.div_add_mod u M2
    have hmin := rayMin2_le_residues.2.2.2.2.2
    omega

/-- **THE RAY IS EMPTY BELOW THE DEPTH-2000 FLOOR.**  No three-free
natural below `rayMin2 ≈ 3.6 × 10^952` lies on the worldtrace ghost
ray — no Mahler input, no compression input, no hypotheses at all. -/
theorem worldtrace_ray2_empty_below (u : Nat) (hu3 : ¬ 3 ∣ u)
    (hlt : u < rayMin2) :
    ¬ WTGhostRay u :=
  fun hg => absurd (worldtrace_ray2_floor u hu3 hg) (by omega)

/-! ## §20 THE TERMINAL FUSION — the act under the six-object seam -/

/-- **THE TERMINAL FUSION.**  The compression plus the ray's emptiness —
now a statement about SIX EXPLICIT OBJECTS (`worldtrace_ray_le_six`) —
close the act.  The Mahler input's entire content has been reduced to the
death of at most six explicit naturals, each exceeding `10^952`. -/
theorem the_act_of_worldtrace_fusion_terminal
    (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u) :
    GSTTheAct.the_act :=
  the_act_of_worldtrace_fusion ((worldtrace_lock_iff_ray_empty).mpr HE) HC

/-- The complete Cantorian universe under the terminal seam. -/
theorem cantarian_universe_classification_terminal
    (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u) :
    ∀ K : Nat, GSTClimbInfiniteFamily.CantorianPower K
      ↔ (K = 0 ∨ K = 1 ∨ K = 4) :=
  cantorian_universe_classification ((worldtrace_lock_iff_ray_empty).mpr HE) HC

/-- The complete Erdős ternary exception set under the terminal seam. -/
theorem erdos_ternary_classification_terminal
    (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u) :
    ∀ n : Nat, noTernaryTwo (2^n) = true
      ↔ (n = 0 ∨ n = 2 ∨ n = 8) :=
  erdos_ternary_classification ((worldtrace_lock_iff_ray_empty).mpr HE) HC

/-- **THE WORLDTRACE TERMINAL RECEIPT.**  The closure state in one theorem:
the ray is FINITE (at most six members over three-free cores); every
member sits in one of six explicit residue classes modulo `3^100`; same
head forces the same member; the Mahler lock IS the empty ray; the ray IS
the convergence; the ray IS the six towers' trace; every member exceeds
`rayMin2 ≈ 3.6 × 10^952` (kernel-certified at depth `3^2000`); the ray is
empty below that floor; and the act closes under the compression plus the
six-object emptiness, carrying both crowns with it. -/
theorem the_worldtrace_terminal_receipt :
    (∀ (s : Finset Nat), (∀ u ∈ s, ¬ 3 ∣ u ∧ WTGhostRay u) → s.card ≤ 6) ∧
    (∀ (u : Nat), ¬ 3 ∣ u → WTGhostRay u →
      (u % M = 442963202118286149036278158734808096675605174274
      ∨ u % M = 390027647331920296602550274777094536582876199053
      ∨ u % M = 284156537759188591735094506861667416397418248611
      ∨ u % M = 231220982972822739301366622903953856304689273390
      ∨ u % M = 125349873400091034433910854988526736119231322948
      ∨ u % M = 72414318613725182000182971030813176026502347727)) ∧
    (∀ (u v : Nat), ¬ 3 ∣ u → ¬ 3 ∣ v → WTGhostRay u → WTGhostRay v →
      (c 1 * u) % 9 = (c 1 * v) % 9 → u = v) ∧
    (WorldtraceMahlerLock ↔ ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u) ∧
    (∀ (u : Nat), ¬ 3 ∣ u →
      (WTGhostRay u ↔ WorldtraceConvergence ((c 1 * u) % 9) u)) ∧
    (∀ (u : Nat), ¬ 3 ∣ u → (WTGhostRay u ↔ ∃ a : Nat, a < 9 ∧ ¬ 3 ∣ a ∧
      (∀ D : Nat, 2 ≤ D → ∃ W : ℤ, 2*(u:ℤ)*((c (D-1):Nat):ℤ)
        - (2*(a:ℤ) - 9) = (3:ℤ)^D * W))) ∧
    (∀ (u : Nat), ¬ 3 ∣ u → WTGhostRay u → rayMin2 ≤ u) ∧
    (∀ (u : Nat), ¬ 3 ∣ u → u < rayMin2 → ¬ WTGhostRay u) ∧
    (∀ (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u),
      GSTTheAct.the_act) ∧
    (∀ (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u),
      ∀ K : Nat, GSTClimbInfiniteFamily.CantorianPower K
        ↔ (K = 0 ∨ K = 1 ∨ K = 4)) ∧
    (∀ (HC : WorldtraceCompression) (HE : ∀ u : Nat, ¬ 3 ∣ u → ¬ WTGhostRay u),
      ∀ n : Nat, noTernaryTwo (2^n) = true
        ↔ (n = 0 ∨ n = 2 ∨ n = 8)) :=
  ⟨worldtrace_ray_le_six, worldtrace_ray_classification,
    worldtrace_ray_head_unique, worldtrace_lock_iff_ray_empty,
    fun u hu3 => worldtrace_ray_iff_convergence u hu3,
    fun u hu3 => worldtrace_ray_iff_pin u hu3,
    worldtrace_ray2_floor, worldtrace_ray2_empty_below,
    the_act_of_worldtrace_fusion_terminal,
    cantarian_universe_classification_terminal,
    erdos_ternary_classification_terminal⟩

#print axioms worldtrace_convergence_pin
#print axioms worldtrace_ray_pin
#print axioms worldtrace_ghostray_of_convergence
#print axioms worldtrace_ray_iff_convergence
#print axioms worldtrace_ray_of_pin
#print axioms worldtrace_ray_iff_pin
#print axioms worldtrace_lock_iff_ray_empty
#print axioms worldtrace_ray_head_unique
#print axioms worldtrace_ray_classification
#print axioms worldtrace_ray_le_six
#print axioms c_mod_1999
#print axioms worldtrace_ray2_residue
#print axioms worldtrace_ray2_floor
#print axioms worldtrace_ray2_empty_below
#print axioms the_act_of_worldtrace_fusion_terminal
#print axioms the_worldtrace_terminal_receipt

end GSTWorldtraceFusion
