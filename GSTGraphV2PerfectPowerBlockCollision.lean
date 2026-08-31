import GSTGraphV2PerfectPowerBlockProbe
import GSTU2DPureDivergence83
import GSTGraphV2CanonicalDescentOntology
import GSTGraphV2CanonicalSignedPrefixBridge
import GSTGraphV2CanonicalInfiniteCycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2PerfectPowerBlockCollision

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2PerfectPowerAncestry
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTGraphV2CoupledUFlux
open GSTU2DPureDivergence83
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalEscape
open GSTGraphV2CanonicalSignedPrefixBridge
open GSTGraphV2CanonicalInfiniteCycle
open GSTGraphV2InfiniteControllerBridge
open GSTV2

/-!
A second phase chart selected by the twelve physical cells.  Unlike the
SURVIVE-aware phase density, this is a *pure* x4/base3 divergence: there is no
interior source term.  Its only positive physical cells are the two Happy
states.  It is used below as a boundary certificate for the canonical
perfect-power strip.
-/

def blockDigitPotential (d : Nat) : Int :=
  if d = 0 then -64 else if d = 1 then -8 else 0

def blockCarryPotential (C : Nat) : Int :=
  if C = 0 then 21 else if C = 1 then 7 else if C = 2 then -1 else -3

def blockDensity (C d : Nat) : Int :=
  blockDigitPotential (outDigit C d) - blockDigitPotential d +
    blockCarryPotential C - 3 * blockCarryPotential (nextCarry C d)

theorem blockDensity_physical_table :
    blockDensity 0 0 = -42 ∧ blockDensity 0 1 = 0 ∧ blockDensity 0 2 = 24 ∧
    blockDensity 1 0 = 0 ∧ blockDensity 1 1 = -6 ∧ blockDensity 1 2 = -48 ∧
    blockDensity 2 0 = 0 ∧ blockDensity 2 1 = -54 ∧ blockDensity 2 2 = 0 ∧
    blockDensity 3 0 = -24 ∧ blockDensity 3 1 = 0 ∧ blockDensity 3 2 = 6 := by
  decide

theorem happy_iff_blockDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < blockDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [HappyCell, blockDensity, blockDigitPotential,
      blockCarryPotential, outDigit, nextCarry]

theorem blockDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    blockDensity C d ≤ 0 := by
  have hiff := happy_iff_blockDensity_positive C d hC hd
  by_contra h
  have hpos : 0 < blockDensity C d := by omega
  exact hbad (hiff.mpr hpos)

/-- Exact vertical telescope of the pure density in one graph column. -/
theorem blockDensity_column_exact
    (E t b K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        blockDensity
          (graph E t (b+j)).seven.carry
          (graph E t (b+j)).seven.digit) =
      Finset.sum (Finset.range K) (fun j =>
        (((3^j : Nat) : Int)) *
          (blockDigitPotential (graph E (t+1) (b+j)).seven.digit -
           blockDigitPotential (graph E t (b+j)).seven.digit)) +
      blockCarryPotential (graph E t b).seven.carry -
        (((3^K : Nat) : Int)) *
          blockCarryPotential (graph E t (b+K)).seven.carry := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have hc := graph_cell_exact E t (b+K)
      rw [blockDensity, hc.1]
      have hcarry :
          nextCarry (graph E t (b+K)).seven.carry
              (graph E t (b+K)).seven.digit =
            (graph E t (b+(K+1))).seven.carry := by
        simpa [Nat.add_assoc] using hc.2
      rw [hcarry, Nat.pow_succ]
      push_cast
      ring

/-- All-depth badness makes every finite pure-density observation nonpositive. -/
theorem blockDensity_prefix_nonpositive_of_bad
    (E t b K : Nat)
    (hBad : ∀ j, j < K → ¬ HappyCell
      (graph E t (b+j)).seven.carry
      (graph E t (b+j)).seven.digit) :
    Finset.sum (Finset.range K) (fun j =>
      (((3^j : Nat) : Int)) *
        blockDensity
          (graph E t (b+j)).seven.carry
          (graph E t (b+j)).seven.digit) ≤ 0 := by
  apply Finset.sum_nonpos
  intro j hj
  have hjK := Finset.mem_range.mp hj
  have hlocal := blockDensity_nonpositive_of_not_happy
    (graph E t (b+j)).seven.carry
    (graph E t (b+j)).seven.digit
    (graph_carry_lt_four E t (b+j))
    (graph_digit_lt_three E t (b+j))
    (hBad j hjK)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlocal

/-- Exact Aug-23 target: a certified child Happy event on the canonical
perfect-power sheet cannot coexist with an all-depth bad right boundary one
`3^s` block later. -/
theorem canonical_perfect_power_block_collision
    (s n q : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hChild : HappyCell
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.carry
      (graph (canonicalEnergy s n) 0 (s+2+q)).seven.digit)
    (hRightBad : ∀ j, ¬ HappyCell
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.carry
      (graph (canonicalEnergy s n) (canonicalWidth s) (s+2+j)).seven.digit) :
    False := by
  let E := canonicalEnergy s n
  let N := canonicalWidth s
  let b := s + 2
  let M := 3^(s+1) * n

  have hN : 1 ≤ N := by
    dsimp [N, canonicalWidth]
    exact Nat.one_le_pow _ _ (by decide)

  have hleft :
      0 < graphPhaseWindow E 0 b (q+1) := by
    apply graph_phase_window_positive_of_happy
    simpa [E, b, Nat.add_assoc] using hChild

  have hright :
      graphPhaseWindow E N b (q+1) ≤ 0 := by
    apply graph_phase_window_nonpositive_of_bad
    intro j hj
    simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hChildSeed :
      SeedHappy 0 0 (canonicalChildTail s n) q := by
    apply (canonical_left_seed_adapter s n q hs).mp
    simpa [E, canonicalEnergy, Nat.add_assoc] using hChild

  have hRightSeed : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j := by
    intro j hSeed
    apply hRightBad j
    have hGraph := (canonical_right_seed_adapter s n j hs).mpr hSeed
    simpa [E, N, b, canonicalEnergy, canonicalWidth, Nat.add_assoc] using hGraph

  have hSignedGrowth :=
    canonical_graph_u_potential_growth_positive
      s n q hs hChildSeed hRightSeed

  have hInfiniteControl :
      InfiniteBadCoupledControl (4^N) (graphCoupledState E N b) := by
    apply graph_infinite_bad_control
    · simpa [E, b, canonicalEnergy] using canonical_base_carry_zero s n hs
    · intro j
      simpa [E, N, b, Nat.add_assoc] using hRightBad j

  have hLiveGate :
      LatentGateTransfer (4^N) (graphCoupledState E N b) q := by
    apply graph_child_happy_latent_transfer
    · simpa [E, b, canonicalEnergy] using canonical_base_carry_zero s n hs
    · intro j
      simpa [E, N, b, Nat.add_assoc] using hRightBad j
    · simpa [E, b, Nat.add_assoc] using hChild

  have hInfiniteLedger :
      InfiniteCoupledLedger (4^N) (graphCoupledState E N b) := by
    apply infinite_coupled_ledger
    · positivity
    · exact graphCoupledState_invariant E N b

  have hGraphSpaceTime : ∀ K,
      coupledOrbit (4^N) (graphCoupledState E N b) K =
        graphCoupledState E N (b + K) := by
    exact graphCoupledOrbit_exact E N b

  have hleftAbs : HappyCell
      (graph 1 M (b+q)).seven.carry
      (graph 1 M (b+q)).seven.digit := by
    have hiff := canonical_power_origin_happy_iff s n 0 (b+q)
    exact hiff.mp (by simpa [E, b, Nat.add_assoc] using hChild)

  have hrightAbs : ∀ j, ¬ HappyCell
      (graph 1 (M+N) (b+j)).seven.carry
      (graph 1 (M+N) (b+j)).seven.digit := by
    intro j h
    apply hRightBad j
    have hiff := canonical_power_origin_happy_iff s n N (b+j)
    exact hiff.mpr (by simpa [M, N] using h)

  have hU := unified_equationIII_vertical_telescope E N b (q+1)
  have hPureRight := blockDensity_prefix_nonpositive_of_bad E N b (q+1)
    (fun j hj => by simpa [E, N, b, Nat.add_assoc] using hRightBad j)
  have hPureExact := blockDensity_column_exact E N b (q+1)

  -- Diagnostic compiler state: expose the exact remaining arithmetic seam.
  dsimp [E, N, b, M] at hleft hright hSignedGrowth hleftAbs hrightAbs hU hPureRight hPureExact hInfiniteControl hLiveGate hInfiniteLedger hGraphSpaceTime ⊢
  trace_state
  omega

#check blockDensity_physical_table
#check happy_iff_blockDensity_positive
#check blockDensity_column_exact
#check canonical_perfect_power_block_collision
#print axioms blockDensity_column_exact
#print axioms canonical_perfect_power_block_collision

end GSTGraphV2PerfectPowerBlockCollision

-- exact full-field ontology probe trigger: 2026-08-30-b
