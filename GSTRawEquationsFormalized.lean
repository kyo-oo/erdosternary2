import GSTPrefixOnePhaseIncidenceControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2
open GSTV2

namespace GSTRawEquations

/-!
# Formalization of the two raw handwritten GST equations

The handwritten pages are treated as operator specifications, not as ordinary
real-analysis notation.  Their intended all-space/all-time content is captured
by exact Nat/Int identities already native to GST V2.

Equation I  : GST Omega-Infinity Navigation-Nullspace Flux Equation.
Equation II : GST Three-World Exponential Coupling Equation.
-/

/-- Equation I: exact all-depth weighted U-flux.  `K` is an arbitrary
observation height; the upper carry stays live.  No terminal state or finite
support hypothesis occurs in the statement. -/
theorem gst_omega_navigation_nullspace_flux_equation
    (D X K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      ((3^j : Nat) : Int) *
        gstHandwrittenUJumpS
          (gstAffineCarryS D X j) (gstDigitS X j)) =
      ((3^K : Nat) : Int) *
          (gstHandwrittenUChargeS (gstAffineCarryS D X K) : Int) -
        (gstHandwrittenUChargeS D : Int) -
        24 * (X % 3^K : Int) := by
  induction K with
  | zero => simp [gstAffineCarryS]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, gstHandwrittenUJumpS,
        gstAffineCarryS_forward_exact_all,
        gst_prefix_residue_succ_exactS, Nat.pow_succ]
      push_cast
      ring

/-- Equation II, microscopic form: the mixed six-world exponential is exactly
binary-world energy times ternary-world energy at every depth. -/
theorem gst_three_world_exponential_coupling_equation
    (j : Nat) :
    6^j = 2^j * 3^j := by
  rw [show (6:Nat) = 2 * 3 by decide, mul_pow]

/-- Equation II, joined BIG-N form: every completed microscopic world carries
aligned `2^j*3^j` mass and the boundary carries the terminal four-unit packet.
This is the literal finite coordinate extracted from the handwritten all-world
operator; it is exact for every positive BIG-N. -/
theorem gst_three_world_bigN_joined_equation
    (a d : Nat → Nat)
    (hpath : GSTInfiniteBridgePathS a d)
    (h0 : d 0 ≠ 0)
    (N : Nat) (hN : 1 ≤ N)
    (hbig : GSTInformationEqualsBigNS d N) :
    gstBig1ProjectedPathCodeS a d N =
      5 * Finset.sum (Finset.range (N-1)) (fun j => 2^j * 3^j) +
        4 * (2^(N-1) * 3^(N-1)) := by
  exact gst_information_eq_bigN_exact_sum_equationS
    a d hpath h0 N hN hbig

/-- The complete canonical parent width closes the same three-world triangle:
its binary multiplier times its ternary scale is the mixed six-world scale. -/
theorem gst_three_world_parent_width_equation
    (s : Nat) :
    4^(3^s) * 3^(2 * 3^s) = 6^(2 * 3^s) := by
  exact gpt56_parent_segment_three_world_factorS s

#check gst_omega_navigation_nullspace_flux_equation
#check gst_three_world_exponential_coupling_equation
#check gst_three_world_bigN_joined_equation
#check gst_three_world_parent_width_equation
#print axioms gst_omega_navigation_nullspace_flux_equation
#print axioms gst_three_world_exponential_coupling_equation
#print axioms gst_three_world_bigN_joined_equation
#print axioms gst_three_world_parent_width_equation

end GSTRawEquations
