import GSTGraphV2InfiniteCardinalMasterScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite eleven-equation synthesis: path / six-world / kernel / cardinal master

This file fuses the exact arithmetic that previously appeared as separate
handwritten/GST identities.  The infinite object is primary: `a,d : Nat -> Nat`
is one actual all-depth microscopic bridge path.  `q` is only an observation
coordinate of that path.

On the nonzero pathwise `I != BIG1` sector every microscopic state has
mass 5 and event 8.  Therefore:

* its base-six prefix is `55...55_6 = 6^q - 1`;
* `6^q - 1 = 5 * sum_{j<q} 6^j` is the exact six-world coefficient;
* the mass-side handwritten kernel `7/(6-m)` is exactly 7 at every depth;
* the event-side signed pole has denominator `J-6 = 2`, hence the
  denominator-cleared resolvent `(J-6)*7 = 14`;
* the arbitrary-cardinality world equation at `K=6^q` has coefficient
  `6^q-1`, so that coefficient is literally the observed code of the one
  infinite path.

The resulting kernel-weighted master equation is

  28 * D_R(6^q) = 7 * E_R(6^q) + KInf(q) * C_R(6^q),

where

  KInf(q) = sum_{j<q} (7 * mass_j) * 6^j
          = 7 * (6^q - 1)
          = 35 * sum_{j<q} 6^j.

No axiom, sorry, admit, or finite substitute for infinity is introduced.
-/

/-- The geometric six-world observation below depth `q`. -/
def gstInfiniteSixWorldPrefixS (q : Nat) : Nat :=
  Finset.sum (Finset.range q) (fun j => 6^j)

/-- Exact six-world closed form, denominator-cleared. -/
theorem gst_infinite_six_world_prefix_closedS (q : Nat) :
    5 * gstInfiniteSixWorldPrefixS q = 6^q - 1 := by
  induction q with
  | zero => simp [gstInfiniteSixWorldPrefixS]
  | succ q ih =>
      unfold gstInfiniteSixWorldPrefixS at ih ⊢
      rw [Finset.sum_range_succ, Nat.mul_add, ih, Nat.pow_succ]
      have hp : 0 < 6^q := Nat.pow_pos (by decide)
      omega

/-- Kernel-weighted code of the observed part of one infinite microscopic path. -/
def gstInfiniteKernelWorldCoefficientS
    (a d : Nat → Nat) (q : Nat) : Nat :=
  Finset.sum (Finset.range q)
    (fun j => 7 * gstBinaryBridgeMassS (a j) (d j) * 6^j)

/-- The infinite `I != BIG1` path has exact kernel coefficient
`7*(6^q-1)` at every observation scale. -/
theorem gst_noBig1_kernel_world_coefficient_exactS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ q,
      gstInfiniteKernelWorldCoefficientS a d q = 7 * (6^q - 1) := by
  intro q
  induction q with
  | zero => simp [gstInfiniteKernelWorldCoefficientS]
  | succ q ih =>
      have hedge := gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 q
      unfold gstInfiniteKernelWorldCoefficientS at ih ⊢
      rw [Finset.sum_range_succ, ih, hedge.2.2.2.1, Nat.pow_succ]
      have hp : 0 < 6^q := Nat.pow_pos (by decide)
      omega

/-- Same coefficient written in the six-world geometric basis.  The local
coefficient 35 is the exact `mass 5 * kernel 7` density. -/
theorem gst_noBig1_kernel_world_coefficient_eq_thirtyfive_prefixS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ q,
      gstInfiniteKernelWorldCoefficientS a d q =
        35 * gstInfiniteSixWorldPrefixS q := by
  intro q
  rw [gst_noBig1_kernel_world_coefficient_exactS a d hpath h0 q]
  have hsix := gst_infinite_six_world_prefix_closedS q
  omega

/-- The path code itself is the arbitrary-cardinality coefficient at the
world `K = 6^q`. -/
theorem gst_noBig1_path_code_is_cardinal_coefficientS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ q,
      gstBig1ProjectedPathCodeS a d q = 6^q - 1 :=
  gst_big1_clear_infinite_all_six_prefixes_maximalS a d hpath h0

/-- First genuinely fused master equation.  The coefficient in the exact
`K=6^q` cardinal-world law is not an external scalar: it is the base-six code
of the first `q` cells of the one infinite `I != BIG1` path. -/
theorem gst_infinite_path_cardinal_master_chordS
    (R : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ q,
      4 * gstCardinalInputEvalS R (6^q) (R+1) =
        gstCardinalOutputEvalS R (6^q) (R+1) +
          gstBig1ProjectedPathCodeS a d q *
            gstCardinalCarryEvalS R (6^q) (R+1) := by
  intro q
  have hcard := gst_cardinal_master_six_powS R q
  have hcode := gst_noBig1_path_code_is_cardinal_coefficientS
    a d hpath h0 q
  rw [hcode]
  exact hcard

/-- Kernel-weighted infinite cardinal conservation.  This is the same exact
cardinal equation after the microscopic kernel value seven has been absorbed
into the path coefficient.

  28 D = 7 E + KInf C.
-/
theorem gst_infinite_kernel_cardinal_masterS
    (R : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ q,
      28 * gstCardinalInputEvalS R (6^q) (R+1) =
        7 * gstCardinalOutputEvalS R (6^q) (R+1) +
          gstInfiniteKernelWorldCoefficientS a d q *
            gstCardinalCarryEvalS R (6^q) (R+1) := by
  intro q
  have hcard := gst_infinite_path_cardinal_master_chordS R a d hpath h0 q
  have hk := gst_noBig1_kernel_world_coefficient_exactS a d hpath h0 q
  have hcode := gst_noBig1_path_code_is_cardinal_coefficientS a d hpath h0 q
  rw [hcode] at hcard
  rw [hk]
  nlinarith

/-- Event-side denominator-cleared handwritten pole equation on every edge of
the same infinite path.  Here `x` is the event symbol `J`, so `J=8` and
`(J-6)*7=14`. -/
theorem gst_noBig1_event_pole_resolvent_all_scalesS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      (((gstBinaryBridgeEventS (a j) (d j) : Int) - 6) * 7 = 14) := by
  intro j
  have hedge := gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 j
  rw [hedge.2.2.2.2]
  norm_num

/-- Mass-side denominator-cleared kernel equation on every edge.  Here `x` is
physical six-state mass, so `m=5` and `(6-m)*7=7`. -/
theorem gst_noBig1_mass_kernel_resolvent_all_scalesS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ j,
      (6 - gstBinaryBridgeMassS (a j) (d j)) * 7 = 7 := by
  intro j
  have hedge := gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 j
  rw [hedge.2.2.2.1]

/-- Eleven-equation synthesis interface.  Every field is derived from the same
infinite path and exact arithmetic; this is useful as a single socket for the
Omega/Navigation adapter. -/
structure GSTInfiniteElevenEquationMasterS
    (R : Nat) (a d : Nat → Nat) : Prop where
  allBig2 : ∀ j, d j = 2
  allMassFive : ∀ j, gstBinaryBridgeMassS (a j) (d j) = 5
  allEventEight : ∀ j, gstBinaryBridgeEventS (a j) (d j) = 8
  allChordThirtyFive : ∀ j,
    gstBinaryBridgeMassS (a j) (d j) +
      6 * gstBinaryBridgeMassS (a (j+1)) (d (j+1)) = 35
  allPathCodes : ∀ q, gstBig1ProjectedPathCodeS a d q = 6^q - 1
  allSixWorldPrefixes : ∀ q, 5 * gstInfiniteSixWorldPrefixS q = 6^q - 1
  allKernelCoefficients : ∀ q,
    gstInfiniteKernelWorldCoefficientS a d q = 7 * (6^q - 1)
  allThirtyFivePrefixes : ∀ q,
    gstInfiniteKernelWorldCoefficientS a d q =
      35 * gstInfiniteSixWorldPrefixS q
  allCardinalChords : ∀ q,
    4 * gstCardinalInputEvalS R (6^q) (R+1) =
      gstCardinalOutputEvalS R (6^q) (R+1) +
        gstBig1ProjectedPathCodeS a d q *
          gstCardinalCarryEvalS R (6^q) (R+1)
  allKernelCardinalChords : ∀ q,
    28 * gstCardinalInputEvalS R (6^q) (R+1) =
      7 * gstCardinalOutputEvalS R (6^q) (R+1) +
        gstInfiniteKernelWorldCoefficientS a d q *
          gstCardinalCarryEvalS R (6^q) (R+1)
  allDualPoleResolvents : ∀ j,
    (((gstBinaryBridgeEventS (a j) (d j) : Int) - 6) * 7 = 14) ∧
      (6 - gstBinaryBridgeMassS (a j) (d j)) * 7 = 7

/-- One nonzero all-depth `I != BIG1` path simultaneously satisfies the eleven
exact equations above. -/
theorem gst_infinite_eleven_equation_masterS
    (R : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    GSTInfiniteElevenEquationMasterS R a d := by
  refine {
    allBig2 := gst_big1_clear_infinite_nonzero_forces_all_big2S a d hpath h0
    allMassFive := ?_
    allEventEight := ?_
    allChordThirtyFive := gst_big1_clear_infinite_every_window_chord35S a d hpath h0
    allPathCodes := gst_noBig1_path_code_is_cardinal_coefficientS a d hpath h0
    allSixWorldPrefixes := gst_infinite_six_world_prefix_closedS
    allKernelCoefficients := gst_noBig1_kernel_world_coefficient_exactS a d hpath h0
    allThirtyFivePrefixes := gst_noBig1_kernel_world_coefficient_eq_thirtyfive_prefixS a d hpath h0
    allCardinalChords := gst_infinite_path_cardinal_master_chordS R a d hpath h0
    allKernelCardinalChords := gst_infinite_kernel_cardinal_masterS R a d hpath h0
    allDualPoleResolvents := ?_ }
  · intro j
    exact (gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 j).2.2.2.1
  · intro j
    exact (gst_big1_clear_infinite_edges_are_surviveS a d hpath h0 j).2.2.2.2
  · intro j
    exact ⟨gst_noBig1_event_pole_resolvent_all_scalesS a d hpath h0 j,
      gst_noBig1_mass_kernel_resolvent_all_scalesS a d hpath h0 j⟩

end GSTInfiniteV2
