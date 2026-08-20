import GSTGraphV2Scratch
import HandwrittenOmegaOperatorScratch
import HandwrittenBig1PathProjectorScratch
import HandwrittenUniversalParadoxPotentialScratch
import HandwrittenX6UPotentialChordScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-!
# GST Graph V2 — controlled infinite-scale layer

This module does not replace an infinite object by a large finite cutoff.
Every wave below is indexed by all natural depths.  Finite sums/codes are only
coordinate projections of that infinite object, and the theorems quantify over
all projection depths.

The handwritten vocabulary retained here is:
* Omega-infinity: all natural transfer coordinates simultaneously;
* Pi: exact simultaneous multiply/divide conservation at every origin depth;
* U: the exact GST bad-language potential at every graph depth;
* 6^k: every finite base-six projection of one infinite microscopic path;
* I != BIG1: pathwise BIG1-clear information, not a global mirror axiom;
* BIG-N: the natural Navigation information packet, viewed on an infinite
  index set with exact eventual stabilization rather than a bounded sum.
-/

/-- An exact natural-valued infinite sum is represented by stabilization of
all sufficiently deep prefix sums.  The index set is genuinely `Nat`; the
cutoff is a theorem-produced stabilization coordinate, not the domain. -/
def GSTControlledInfiniteSumS (f : Nat → Nat) (total : Nat) : Prop :=
  ∃ K0, ∀ K, K0 ≤ K → (∑ i in Finset.range K, f i) = total

/-- Boss's Omega transfer packet is an infinite indexed object whose prefix
sums stabilize exactly at the full Navigation energy transfer. -/
theorem gst_omega_natural_transfer_infinite_controlS
    (t T : Nat) :
    GSTControlledInfiniteSumS
      (gstOmegaNaturalTransferS t T) (3^(t+1) * T) := by
  refine ⟨T + 1, ?_⟩
  intro K hK
  rw [gst_omega_natural_transfer_prefixS]
  have hbase : T < 3^(T+1) := gst_three_pow_succ_gt_pressureS T
  have hpow : 3^(T+1) ≤ 3^K :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hK
  have hlt : T < 3^K := lt_of_lt_of_le hbase hpow
  rw [Nat.mod_eq_of_lt hlt]

/-- BIG-N branch: the Navigation packet is controlled on all natural indices,
and its stabilized Omega transfer reconstructs the exact pressure energy. -/
theorem gst_handwritten_bigN_infinite_energy_controlS
    (t N : Nat) :
    GSTControlledInfiniteSumS
        (gstOmegaNaturalTransferS t N) (3^(t+1) * N) ∧
      1 + 3^(t+1) * N = gstOmegaPressureEnergyS t N := by
  constructor
  · exact gst_omega_natural_transfer_infinite_controlS t N
  · rfl

/-- The handwritten simultaneous multiply/divide glyph is promoted to an
all-scales law: at every origin depth K, consumed U times remaining U is the
same original perfect-power energy. -/
def GSTOriginInfiniteMulDivControlS (t n : Nat) : Prop :=
  ∀ K,
    gstOriginConsumedPrefixUS t n K *
        gstOriginRemainingUS (t+K) (n / 3^K) =
      gstOriginRemainingUS t n

theorem gst_origin_infinite_mul_div_controlS
    (t n : Nat) : GSTOriginInfiniteMulDivControlS t n := by
  intro K
  exact gst_origin_prefix_remaining_U_conservationS t n K

/-- One state of the Pi/Omega origin controller at arbitrary depth K. -/
structure GSTOriginInfinityStateS where
  scale : Nat
  remainingOrigin : Nat
  consumedU : Nat
  remainingU : Nat
  deriving Repr

def gstOriginInfinityStateS (t n K : Nat) : GSTOriginInfinityStateS where
  scale := t + K
  remainingOrigin := n / 3^K
  consumedU := gstOriginConsumedPrefixUS t n K
  remainingU := gstOriginRemainingUS (t+K) (n / 3^K)

/-- Every state of the infinite Pi controller lies on the same exact U-energy
hypersurface. -/
theorem gst_origin_infinity_state_energy_invariantS
    (t n K : Nat) :
    (gstOriginInfinityStateS t n K).consumedU *
        (gstOriginInfinityStateS t n K).remainingU =
      gstOriginRemainingUS t n := by
  simpa [gstOriginInfinityStateS] using
    gst_origin_prefix_remaining_U_conservationS t n K

/-- The seven-axis V2 graph itself is an actual infinite orbit: there is one
canonical vertex at every natural information depth. -/
def gstGraphV2InfiniteOrbitS (R N : Nat) : Nat → GSTSevenAxisVertexV2S :=
  fun p => gstSevenAxisVertexV2S R N p

theorem gst_graph_v2_infinite_orbit_coordinatesS
    (R N p : Nat) :
    (gstGraphV2InfiniteOrbitS R N p).x = p ∧
      (gstGraphV2InfiniteOrbitS R N p).xNext = p+1 ∧
      (gstGraphV2InfiniteOrbitS R N p).carry = gstCarryS R p ∧
      (gstGraphV2InfiniteOrbitS R N p).digit = gstDigitS R p ∧
      (gstGraphV2InfiniteOrbitS R N p).descent = R / 3^p ∧
      (gstGraphV2InfiniteOrbitS R N p).nextDescent = R / 3^(p+1) := by
  rfl

/-- Exact edge law at every point of the infinite V2 orbit. -/
theorem gst_graph_v2_infinite_orbit_stepS
    (R N p : Nat) :
    (gstGraphV2InfiniteOrbitS R N (p+1)).carry =
      gstStepCarryS
        (gstGraphV2InfiniteOrbitS R N p).carry
        (gstGraphV2InfiniteOrbitS R N p).digit := by
  simpa [gstGraphV2InfiniteOrbitS, gstSevenAxisVertexV2S] using
    gstCarryS_forward_exact_all R p

/-- The handwritten 7/(x-6) microscopic pole is safe at every coordinate of
any legal infinite binary/ternary bridge path: physical event symbol 6 never
appears. -/
theorem gst_handwritten_event_pole_six_avoided_infiniteS
    (a d : Nat → Nat)
    (ha : ∀ j, a j < 2)
    (hd : ∀ j, d j < 3) :
    ∀ j, gstBinaryBridgeEventS (a j) (d j) ≠ 6 := by
  intro j
  exact gst_binary_bridge_event_ne_sixS (a j) (d j) (ha j) (hd j)

/-- Infinite pathwise version of the handwritten `I != BIG1` projector. -/
structure GSTBig1ClearInfinitePathS (a d : Nat → Nat) : Prop where
  bit_lt_two : ∀ j, a j < 2
  digit_lt_three : ∀ j, d j < 3
  information_ne_big1 : ∀ j, d j ≠ 1
  bridge_step : ∀ j, gstBinaryBridgeOutputS (a j) (d j) = d (j+1)

/-- Every finite coordinate window is a projection of the same infinite
BIG1-clear path. -/
theorem gst_big1_clear_infinite_prefixS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (K : Nat) :
    GSTBig1ClearBridgePathS a d K := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    exact h.bit_lt_two j
  · intro j hj
    exact h.digit_lt_three j
  · intro j hj
    exact h.information_ne_big1 j
  · intro j hj
    exact h.bridge_step j

/-- Infinite `I != BIG1` rigidity: one nonzero initial information state forces
BIG2 at every information depth, with no terminal depth. -/
theorem gst_big1_clear_infinite_nonzero_forces_all_big2S
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j, d j = 2 := by
  intro j
  have hp : GSTBig1ClearBridgePathS a d j :=
    gst_big1_clear_infinite_prefixS a d h j
  exact gst_big1_clear_path_nonzero_forces_all_big2S
    a d j hp h0 j (by omega)

/-- Every microscopic edge of the infinite BIG1-clear nonzero branch is the
unique SURVIVE state: bit 1, information BIG2, mass 5, event 8. -/
theorem gst_big1_clear_infinite_edges_are_surviveS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      a j = 1 ∧ d j = 2 ∧
      gstBinaryBridgeOutputS (a j) (d j) = 2 ∧
      gstBinaryBridgeMassS (a j) (d j) = 5 ∧
      gstBinaryBridgeEventS (a j) (d j) = 8 := by
  intro j
  have hp : GSTBig1ClearBridgePathS a d (j+1) :=
    gst_big1_clear_infinite_prefixS a d h (j+1)
  exact gst_big1_clear_path_edges_are_surviveS
    a d (j+1) hp h0 j (by omega)

/-- Every consecutive two-edge window of that one infinite branch is the same
physical right chord 55_6 = 35.  Thus the chord is not a one-off finite cell;
it is controlled at every translation of the infinite information axis. -/
theorem gst_big1_clear_infinite_every_window_chord35S
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      gstBinaryBridgeMassS (a j) (d j) +
        6 * gstBinaryBridgeMassS (a (j+1)) (d (j+1)) = 35 := by
  intro j
  have hj := gst_big1_clear_infinite_edges_are_surviveS a d h h0 j
  have hj1 := gst_big1_clear_infinite_edges_are_surviveS a d h h0 (j+1)
  rw [hj.2.2.2.1, hj1.2.2.2.1]

/-- The full 6^k content is controlled simultaneously: every finite base-six
projection of the infinite `I != BIG1` branch is exactly the maximal word
55...55, value 6^K-1. -/
theorem gst_big1_clear_infinite_all_six_prefixes_maximalS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ K, gstBig1ProjectedPathCodeS a d K = 6^K - 1 := by
  intro K
  exact gst_big1_projected_path_code_eq_six_pow_sub_oneS
    a d K (gst_big1_clear_infinite_prefixS a d h K) h0

/-- Same all-scales statement in the world-projection language already used by
V2: each observation depth sees the exact coefficient 6^K-1. -/
theorem gst_big1_clear_infinite_world_projectionS
    (a d : Nat → Nat)
    (h : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ K,
      gstBig1ProjectedPathCodeS a d K =
        gstWorldProjectionCoefficientS (6^K) := by
  intro K
  exact gst_big1_projected_path_equals_world_projection_coefficientS
    a d K (gst_big1_clear_infinite_prefixS a d h K) h0

/-- U is also promoted from one finite prefix to an all-scales controller.
A complete bad GST trace must satisfy the telescoped U inequality at every
information depth simultaneously. -/
theorem gst_v2_infinite_bad_u_control_all_scalesS
    (D X : Nat) (hD : D < 4)
    (hbad : GSTSeededBadTraceS D X) :
    ∀ K,
      24*(X % 3^K) + gstHandwrittenUChargeS D ≤
        3^K * gstHandwrittenUChargeS
          (gstAffineMulCarryS 4 D X K) := by
  intro K
  exact gst_bad_prefix_u_potential_boundS D X K hD
    (fun j _hj => hbad j)

/-- Infinite x=6 orientation controller.  Whenever the handwritten x-6 fibre
is hit anywhere on a legal V2 orbit, U immediately distinguishes the two
physical orientations; negative curvature is exactly exposed NULL/BIG2. -/
theorem gst_handwritten_x6_infinite_orientation_controlS
    (C d : Nat → Nat)
    (hC : ∀ j, C j < 4)
    (hd : ∀ j, d j < 3)
    (hx : ∀ j, gstHandwrittenXCoordS (C j) (d j) = 6) :
    ∀ j,
      gstHandwrittenUJumpS (C j) (d j) < 0 ↔
        (C j = 0 ∧ d j = 2) := by
  intro j
  exact gst_handwritten_x6_negative_iff_exposedS
    (C j) (d j) (hC j) (hd j) (hx j)
