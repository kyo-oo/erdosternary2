import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle
import GSTGraphV2CanonicalTerminalExtinctionProbe
import GSTGraphV2PerfectPowerBlockProbe
import GSTGraphV2UnifiedVerticalTelescope
import GSTFinalPurePowerResidueTransplant
import GSTGraphV2FourPowerForcingBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTFinalPurePowerResidueTransplant
open GSTU2DEventTransport
open GSTGraphV2NonlocalCascade

/-- Exact universal induction edge to be proved without weakening.

A physical Happy cell on the `4^K` unit sheet must force the existence of
some physical Happy cell on the `4^(K+1)` sheet.  The relocated row is not
assumed to be local to the input row. -/
def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit

/-- A physical Graph-V2 cell is Happy exactly when information digit two is
present at the cell and survives the horizontal x4 step at the same row. -/
theorem graph_happy_iff_consecutive_digit_two
    (E t p : Nat) :
    HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit ↔
      (graph E t p).seven.digit = 2 ∧
        (graph E (t+1) p).seven.digit = 2 := by
  constructor
  · intro hHappy
    rcases hHappy with ⟨hd, hcarry⟩
    refine ⟨hd, ?_⟩
    have hHappy' : HappyCell
        (graph E t p).seven.carry
        (graph E t p).seven.digit := ⟨hd, hcarry⟩
    have hout :=
      (happyCell_positive_and_preserves_big2
        (graph E t p).seven.carry
        (graph E t p).seven.digit hHappy').2
    rw [← (graph_cell_exact E t p).1]
    exact hout
  · rintro ⟨hd, hnext⟩
    refine ⟨hd, ?_⟩
    have hout :
        outDigit
          (graph E t p).seven.carry
          (graph E t p).seven.digit = 2 := by
      rw [(graph_cell_exact E t p).1]
      exact hnext
    have hcarryLt := graph_carry_lt_four E t p
    have hcases :
        (graph E t p).seven.carry = 0 ∨
        (graph E t p).seven.carry = 1 ∨
        (graph E t p).seven.carry = 2 ∨
        (graph E t p).seven.carry = 3 := by
      omega
    rcases hcases with h0 | h1 | h2 | h3
    · exact Or.inl h0
    · rw [h1, hd] at hout
      norm_num [outDigit] at hout
    · rw [h2, hd] at hout
      norm_num [outDigit] at hout
    · exact Or.inr h3

/-- Arithmetic form of the same physical law on a pure four-power sheet.
The carry condition has disappeared completely: a Happy witness is exactly a
shared ternary digit-two position of two consecutive powers of four. -/
theorem four_power_happy_iff_consecutive_digit_two
    (K p : Nat) :
    GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p) ↔
      GSTCanonicalTailStateIso.digit3 (4^K) p = 2 ∧
        GSTCanonicalTailStateIso.digit3 (4^(K+1)) p = 2 := by
  simpa [GSTGraphV2InfiniteControl.graph,
    GSTGraphV2InfiniteControl.cell,
    GSTCanonicalSevenAxisBridge.vertex,
    GSTCanonicalSevenAxisBridge.carry4,
    GSTCanonicalSevenAxisBridge.digit3,
    GSTU2DEventTransport.HappyCell,
    GSTCanonicalTailStateIso.HappyCell,
    GSTCanonicalTailStateIso.carry4,
    GSTCanonicalTailStateIso.digit3] using
      (graph_happy_iff_consecutive_digit_two 1 K p)

/-- The original universal four-power target, isolated from the monolith. -/
def FourPowerCanonicalHappyTarget : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p)

/-- Pure arithmetic form of the exact same target. -/
def FourPowerDigitOverlap : Prop :=
  ∀ K : Nat, 5 ≤ K → K ≠ 7 →
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^K) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(K+1)) p = 2

/-- No weakening is hidden in the digit-overlap reformulation. -/
theorem four_power_canonical_target_iff_digit_overlap :
    FourPowerCanonicalHappyTarget ↔ FourPowerDigitOverlap := by
  constructor
  · intro h K hK5 hK7
    rcases h K hK5 hK7 with ⟨p, hp, hHappy⟩
    exact ⟨p, hp, (four_power_happy_iff_consecutive_digit_two K p).mp hHappy⟩
  · intro h K hK5 hK7
    rcases h K hK5 hK7 with ⟨p, hp, hOverlap⟩
    exact ⟨p, hp, (four_power_happy_iff_consecutive_digit_two K p).mpr hOverlap⟩

/-- Exact base witness at K=5. -/
theorem four_power_digit_overlap_base_5 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^5) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(5+1)) p = 2 := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- Exact base witness at K=6. -/
theorem four_power_digit_overlap_base_6 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^6) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(6+1)) p = 2 := by
  refine ⟨2, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- Exact induction base witness at K=8. -/
theorem four_power_digit_overlap_base_8 :
    ∃ p : Nat, 1 ≤ p ∧
      GSTCanonicalTailStateIso.digit3 (4^8) p = 2 ∧
      GSTCanonicalTailStateIso.digit3 (4^(8+1)) p = 2 := by
  refine ⟨4, by norm_num, ?_, ?_⟩
  · norm_num [GSTCanonicalTailStateIso.digit3]
  · norm_num [GSTCanonicalTailStateIso.digit3]

/-- LTE-specialized exponent-trit transport with no free coefficient
hypothesis.  This is the exact arithmetic bridge used for the power-specific
part of the latent-future analysis. -/
theorem four_power_exponent_trit_lift
    (p m a : Nat) (ha : a < 3) :
    GSTCanonicalSevenAxisBridge.digit3 (4^(m + a*3^p)) (p+1) =
      (GSTCanonicalSevenAxisBridge.digit3 (4^m) (p+1) + a) % 3 := by
  exact GSTFinalPurePowerResidueTransplant.pow4_exponent_trit_lift_digit
    p m (GSTGraphV2HandwrittenExponentialLTE.lteCoeff p) a ha
    (GSTGraphV2HandwrittenExponentialLTE.pow4_three_power_lte_exact p)
    (GSTGraphV2HandwrittenExponentialLTE.lteCoeff_mod3_one p)

/-- A deliberately loose but fully symbolic support cutoff.  It depends only
on `K`; no computational cutoff is baked into the universal argument. -/
def fourPowerSupportCutoff (K : Nat) : Nat := 4^(K+2) + 1

private theorem index_le_three_pow_local (r : Nat) :
    r ≤ 3^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      omega

/-- The cutoff is high enough to dominate the entire `4^(K+1)` physical cell,
including the extra factor four used by the carry observable. -/
theorem four_power_support_cutoff_pow_lt
    (K : Nat) :
    4^((K+1)+1) < 3^(fourPowerSupportCutoff K) := by
  have hlt : 4^((K+1)+1) < fourPowerSupportCutoff K := by
    simp [fourPowerSupportCutoff, show (K+1)+1 = K+2 by omega]
  have hle : fourPowerSupportCutoff K ≤ 3^(fourPowerSupportCutoff K) :=
    index_le_three_pow_local (fourPowerSupportCutoff K)
  omega

/-- Exact pure-power digit extinction at the symbolic cutoff. -/
theorem four_power_digit_zero_at_support_cutoff
    (K : Nat) :
    GSTCanonicalTailStateIso.digit3
      (4^(K+1)) (fourPowerSupportCutoff K) = 0 := by
  have hpow := four_power_support_cutoff_pow_lt K
  have hmono : 4^(K+1) ≤ 4^((K+1)+1) := by
    rw [Nat.pow_succ]
    omega
  have ht : 4^(K+1) < 3^(fourPowerSupportCutoff K) :=
    lt_of_le_of_lt hmono hpow
  simp [GSTCanonicalTailStateIso.digit3, Nat.div_eq_of_lt ht]

/-- Exact physical Graph-V2 neutralization at the same symbolic cutoff. -/
theorem four_power_graph_neutral_at_support_cutoff
    (K : Nat) :
    (graph 1 (K+1) (fourPowerSupportCutoff K)).seven.carry = 0 ∧
      (graph 1 (K+1) (fourPowerSupportCutoff K)).seven.digit = 0 := by
  exact
    GSTGraphV2CanonicalTerminalExtinctionProbe.unit_graph_cell_neutral_of_pow_lt
      (K+1) (fourPowerSupportCutoff K)
      (four_power_support_cutoff_pow_lt K)

/-- Exact vertical future packet beginning one row above a latent x4 cascade.
Nothing is projected away: carry and digit stay on the physical Graph-V2
sheet, carries remain physical, digits remain ternary, and the vertical
recurrence is the literal cell law at every future row. -/
theorem latent_vertical_future_packet
    (K p : Nat)
    (hNext : (graph 1 (K+1) (p+1)).seven.carry = 3) :
    let C : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.carry
    let d : Nat → Nat := fun r =>
      (graph 1 (K+1) (p+1+r)).seven.digit
    C 0 = 3 ∧
      (∀ r, C r < 4) ∧
      (∀ r, d r < 3) ∧
      (∀ r,
        GST2DMixedEmergence.nextCarry (C r) (d r) = C (r+1)) := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hNext
  · intro r
    exact graph_carry_lt_four 1 (K+1) (p+1+r)
  · intro r
    exact graph_digit_lt_three 1 (K+1) (p+1+r)
  · intro r
    simpa [Nat.add_assoc] using
      (graph_cell_exact 1 (K+1) (p+1+r)).2

/-- If no relocated Happy witness exists anywhere above row zero, then every
row in the vertical future of a latent packet is physically bad. -/
theorem future_bad_of_no_relocated_happy
    (K p : Nat)
    (hNoRelocated : ¬ ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit) :
    ∀ r : Nat,
      ¬ HappyCell
        (graph 1 (K+1) (p+1+r)).seven.carry
        (graph 1 (K+1) (p+1+r)).seven.digit := by
  intro r hHappy
  apply hNoRelocated
  exact ⟨p+1+r, by omega, hHappy⟩

/-! ### Fresh power-specific width-three obstruction

The following declarations intentionally rederive the collision chain from
its primitive Graph-V2 dependencies.  They do not import or call the
historical universal four-power navigation theorem. -/

/-- Exact width-three pure-power conservation at the production cut. -/
theorem relocation_width_three_exact_conservation (K q : Nat) :
    64 * (graph (4^K) 0 (3+q)).seven.digit +
        wideCarry 64 (4^K) (3+q) =
      (graph (4^K) 3 (3+q)).seven.digit +
        3 * wideCarry 64 (4^K) ((3+q)+1) := by
  have h := exactPowerRectangle_conservation 1 2 K q
  norm_num [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
    Nat.add_assoc, Nat.pow_add] at h ⊢
  simpa [Nat.mul_comm] using h

/-- Physical Happy cells have strictly negative exact handwritten-U jump. -/
theorem relocation_u_jump_negative_of_happy
    (C d : Nat) (h : HappyCell C d) :
    gstUJumpExact C d < 0 := by
  rcases h with ⟨rfl, h0 | h3⟩
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]
  · subst C
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- Every non-Happy physical cell has nonnegative exact handwritten-U jump. -/
theorem relocation_u_jump_nonnegative_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    0 ≤ gstUJumpExact C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- A disappearing child Happy gate creates a strictly positive exact U defect. -/
theorem relocation_width_three_u_derivative_positive
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRight : ¬ HappyCell
      (graph (4^K) 3 (3+q)).seven.carry
      (graph (4^K) 3 (3+q)).seven.digit) :
    0 <
      3 * potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 ((3+q)+1)).core -
        potentialWith gstUChargeExact (4^3)
          (unifiedState (4^K) 3 (3+q)).core := by
  have hEq := unified_equationIII_graph_closed (4^K) 3 (3+q)
  have hChildNeg := relocation_u_jump_negative_of_happy
    (graph (4^K) 0 (3+q)).seven.carry
    (graph (4^K) 0 (3+q)).seven.digit hChild
  have hRightNonneg := relocation_u_jump_nonnegative_of_not_happy
    (graph (4^K) 3 (3+q)).seven.carry
    (graph (4^K) 3 (3+q)).seven.digit
    (graph_carry_lt_four (4^K) 3 (3+q))
    (graph_digit_lt_three (4^K) 3 (3+q)) hRight
  rw [← hEq]
  norm_num
  nlinarith

/-- Fresh power-specific three-step collision, proved only from exact physical
conservation, phase windows, and the exact vertical telescope. -/
theorem relocation_power_three_step_collision
    (K q : Nat)
    (hChild : HappyCell
      (graph (4^K) 0 (3+q)).seven.carry
      (graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (4^K) 3 (3+j)).seven.carry
      (graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  let E := 4^K
  let N : Nat := 3
  let b : Nat := 3

  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hleftAbs : HappyCell
      (graph 1 K (b+q)).seven.carry
      (graph 1 K (b+q)).seven.digit := by
    have hiff := power_origin_happy_iff K 0 (b+q)
    exact hiff.mp (by simpa [E, b, Nat.add_assoc] using hChild)

  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (K+N) (b+j)).seven.carry
      (graph 1 (K+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := power_origin_happy_iff K N (b+j)
    exact hiff.mpr (by simpa [E, N] using h)

  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hWidth3 := relocation_width_three_exact_conservation K q
  have hUPositive := relocation_width_three_u_derivative_positive K q hChild
    (hRightBad q)

  dsimp [E, N, b] at hleft hright hleftAbs hrightAbs hU hWidth3 ⊢
  dsimp [potentialWith, unifiedState] at hUPositive
  omega

/-- Fresh, standalone consequence of the collision: every pure power from
exponent eight onward contains a physical Happy cell at a row at least three. -/
theorem relocation_four_power_happy_ge_three
    (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^k) p) (digit3 (4^k) p) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk11 : 11 ≤ k
      · have hk3 : 8 ≤ k - 3 := by omega
        obtain ⟨p, hp3, hpHappy⟩ := ih (k - 3) (by omega) hk3
        let q := p - 3
        have hpq : 3 + q = p := by
          dsimp [q]
          omega
        have hChild : HappyCell
            (graph (4^(k-3)) 0 (3+q)).seven.carry
            (graph (4^(k-3)) 0 (3+q)).seven.digit := by
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex, hpq] using hpHappy
        by_contra hno
        have hRightBad : ∀ j, ¬ HappyCell
            (graph (4^(k-3)) 3 (3+j)).seven.carry
            (graph (4^(k-3)) 3 (3+j)).seven.digit := by
          intro j hright
          apply hno
          refine ⟨3+j, by omega, ?_⟩
          have hpow : 4^3 * 4^(k-3) = 4^k := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [← hpow]
          simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hright
        exact relocation_power_three_step_collision (k-3) q hChild hRightBad
      · have hkCases : k = 8 ∨ k = 9 ∨ k = 10 := by omega
        rcases hkCases with rfl | rfl | rfl
        · refine ⟨4, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨7, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]
        · refine ⟨10, by decide, ?_⟩
          norm_num [HappyCell, carry4, digit3]

/-- Physical Graph-V2 form of the fresh `K ≥ 8` existence theorem. -/
theorem relocation_graph_happy_ge_eight
    (k : Nat) (hk : 8 ≤ k) :
    ∃ p : Nat, 1 ≤ p ∧
      HappyCell (graph 1 k p).seven.carry (graph 1 k p).seven.digit := by
  obtain ⟨p, hp3, hHappy⟩ := relocation_four_power_happy_ge_three k hk
  refine ⟨p, by omega, ?_⟩
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hHappy

/-- The exact handoff target.  We first take the already-green local
`Happy → Happy ∨ latent` split.  The direct branch keeps the same row; in the
latent branch the fresh power-specific collision theorem supplies an actual
physical row on the next pure-power sheet. -/
theorem four_power_happy_propagates : FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  rcases four_power_happy_lifts_or_latent K p hHappy with hDirect | hLatent
  · exact ⟨p, hp, hDirect⟩
  · obtain ⟨q, hq, hqHappy⟩ := relocation_graph_happy_ge_eight (K+1) (by omega)
    exact ⟨q, hq, hqHappy⟩

/-- Rebuild all `K ≥ 8` Graph-V2 existence by literal successor induction
using the newly proved one-step propagation edge. -/
theorem relocation_graph_happy_from_eight_by_propagation
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, 1 ≤ p ∧
      HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit := by
  let P : Nat → Prop := fun n =>
    ∃ p : Nat, 1 ≤ p ∧
      HappyCell (graph 1 n p).seven.carry (graph 1 n p).seven.digit
  have h8 : P 8 := by
    dsimp [P]
    refine ⟨4, by norm_num, ?_⟩
    norm_num [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
      HappyCell, carry4, digit3]
  have hstep : ∀ n : Nat, 8 ≤ n → P n → P (n+1) := by
    intro n hn hPn
    rcases hPn with ⟨p, hp, hHappy⟩
    exact four_power_happy_propagates n p hn hp hHappy
  exact Nat.le_induction h8 hstep K hK

/-- Exact production forcing proposition, built from the standalone
propagation theorem plus the finite bases 5 and 6 and the explicit exception 7. -/
theorem four_power_graph_forcing :
    GSTGraphV2FourPowerForcingBridge.FourPowerGraphForcing := by
  intro K hK5 hK7
  by_cases hK8 : 8 ≤ K
  · obtain ⟨p, hp, hHappy⟩ :=
      relocation_graph_happy_from_eight_by_propagation K hK8
    refine ⟨p, hp, ?_⟩
    simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex,
      GSTCanonicalTailStateIso.HappyCell,
      GSTCanonicalTailStateIso.carry4,
      GSTCanonicalTailStateIso.digit3,
      GSTU2DEventTransport.HappyCell,
      GSTCanonicalSevenAxisBridge.carry4,
      GSTCanonicalSevenAxisBridge.digit3] using hHappy
  · have hCases : K = 5 ∨ K = 6 ∨ K = 7 := by omega
    rcases hCases with rfl | rfl | rfl
    · refine ⟨2, by norm_num, ?_⟩
      norm_num [GSTCanonicalTailStateIso.HappyCell,
        GSTCanonicalTailStateIso.carry4,
        GSTCanonicalTailStateIso.digit3]
    · refine ⟨2, by norm_num, ?_⟩
      norm_num [GSTCanonicalTailStateIso.HappyCell,
        GSTCanonicalTailStateIso.carry4,
        GSTCanonicalTailStateIso.digit3]
    · exact (hK7 rfl).elim

/-- Exact historical creation proposition obtained only through the already
proved graph/creation equivalence. -/
theorem four_power_creation_master :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
  GSTGraphV2FourPowerForcingBridge.graph_forcing_to_creation_master
    four_power_graph_forcing

#check FourPowerHappyPropagation
#check FourPowerCanonicalHappyTarget
#check FourPowerDigitOverlap
#check graph_happy_iff_consecutive_digit_two
#check four_power_happy_iff_consecutive_digit_two
#check four_power_canonical_target_iff_digit_overlap
#check four_power_digit_overlap_base_5
#check four_power_digit_overlap_base_6
#check four_power_digit_overlap_base_8
#check four_power_exponent_trit_lift
#check fourPowerSupportCutoff
#check four_power_support_cutoff_pow_lt
#check four_power_digit_zero_at_support_cutoff
#check four_power_graph_neutral_at_support_cutoff
#check latent_vertical_future_packet
#check future_bad_of_no_relocated_happy
#check relocation_width_three_exact_conservation
#check relocation_width_three_u_derivative_positive
#check relocation_power_three_step_collision
#check relocation_four_power_happy_ge_three
#check relocation_graph_happy_ge_eight
#check four_power_happy_propagates
#check relocation_graph_happy_from_eight_by_propagation
#check four_power_graph_forcing
#check four_power_creation_master

#print axioms graph_happy_iff_consecutive_digit_two
#print axioms four_power_happy_iff_consecutive_digit_two
#print axioms four_power_canonical_target_iff_digit_overlap
#print axioms four_power_digit_overlap_base_5
#print axioms four_power_digit_overlap_base_6
#print axioms four_power_digit_overlap_base_8
#print axioms four_power_exponent_trit_lift
#print axioms four_power_support_cutoff_pow_lt
#print axioms four_power_digit_zero_at_support_cutoff
#print axioms four_power_graph_neutral_at_support_cutoff
#print axioms latent_vertical_future_packet
#print axioms future_bad_of_no_relocated_happy
#print axioms relocation_width_three_exact_conservation
#print axioms relocation_width_three_u_derivative_positive
#print axioms relocation_power_three_step_collision
#print axioms relocation_four_power_happy_ge_three
#print axioms relocation_graph_happy_ge_eight
#print axioms four_power_happy_propagates
#print axioms relocation_graph_happy_from_eight_by_propagation
#print axioms four_power_graph_forcing
#print axioms four_power_creation_master

end GSTGraphV2FourPowerRelocation
