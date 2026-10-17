import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite-control contradiction blades

These theorems consume the already kernelized infinite GST V2 controller.
They do not replace infinity by a large finite bound.  Instead they compare an
actual `Nat -> information` infinite path with the finite-support theorem that
is forced by representing that path with one ordinary natural number.
-/

/-- Every ordinary natural ternary stream is zero at all coordinates at or
above its explicit support ceiling `X+1`. -/
theorem gst_natural_digit_stream_eventually_zeroS
    (X j : Nat) (hj : X + 1 ≤ j) :
    gstDigitS X j = 0 := by
  have hbase : X < 3^(X+1) := gst_self_lt_three_pow_succS X
  have hpow : 3^(X+1) ≤ 3^j :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hj
  have hlt : X < 3^j := lt_of_lt_of_le hbase hpow
  unfold gstDigitS
  rw [Nat.div_eq_of_lt hlt]

/-- The infinite `I != BIG1` branch cannot be the ternary information stream
of any ordinary natural.  Infinite rigidity forces BIG2 at every coordinate;
natural finite support forces zero at `X+1`. -/
theorem gst_big1_clear_infinite_cannot_be_natural_digit_streamS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (X : Nat)
    (hreal : ∀ j, d j = gstDigitS X j) : False := by
  have hall := gst_big1_clear_infinite_nonzero_forces_all_big2S
    a d hpath h0
  have htwo : d (X+1) = 2 := hall (X+1)
  have hzeroX : gstDigitS X (X+1) = 0 :=
    gst_natural_digit_stream_eventually_zeroS X (X+1) (by omega)
  have hrealX : d (X+1) = gstDigitS X (X+1) := hreal (X+1)
  omega

/-- Equivalent contradiction written as a genuine all-scale statement: an
ordinary natural cannot carry nonzero ternary information beyond every finite
observation depth. -/
def GSTInfiniteTernarySupportS (X : Nat) : Prop :=
  ∀ K, ∃ j, K ≤ j ∧ gstDigitS X j ≠ 0

theorem gst_natural_not_infinite_ternary_supportS
    (X : Nat) : ¬ GSTInfiniteTernarySupportS X := by
  intro hinf
  obtain ⟨j, hj, hnz⟩ := hinf (X+1)
  exact hnz (gst_natural_digit_stream_eventually_zeroS X j hj)

/-- Infinite BIG1-clear rigidity directly forces infinite ternary support for
any stream claimed to realize it.  Combining with the previous theorem gives
an immediate contradiction. -/
theorem gst_big1_clear_infinite_forces_infinite_supportS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (X : Nat)
    (hreal : ∀ j, d j = gstDigitS X j) :
    GSTInfiniteTernarySupportS X := by
  intro K
  refine ⟨K, le_rfl, ?_⟩
  have htwo := gst_big1_clear_infinite_nonzero_forces_all_big2S
    a d hpath h0 K
  rw [hreal K] at htwo
  omega

/-- Packaged infinite-control blade: a pathwise `I != BIG1` nonzero sector,
when tied to a natural-origin information stream, destroys the finite-support
assumption without any finite witness-depth search. -/
theorem gst_big1_clear_infinite_natural_support_collisionS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (X : Nat)
    (hreal : ∀ j, d j = gstDigitS X j) : False := by
  have hinf : GSTInfiniteTernarySupportS X :=
    gst_big1_clear_infinite_forces_infinite_supportS a d hpath h0 X hreal
  exact gst_natural_not_infinite_ternary_supportS X hinf

end GSTInfiniteV2
