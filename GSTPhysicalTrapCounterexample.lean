import «ker07-snapshot».branches.«15_sol_new__physical-phase-crossing-surgery».CanonicalTrapScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- Concrete seed-zero bad suffix occurring after the child cut in the
    canonical `(s,n)=(2,1)` rectangle. -/
theorem gpt56_concrete_parent_suffix_bad :
    GSTSeededBadTraceS 0 2548470 := by
  intro j
  unfold GSTBadPairS
  intro h
  rcases h with ⟨hd, hc⟩
  by_cases hj : j < 14
  · interval_cases j <;>
      norm_num [gstDigitS, gstAffineMulCarryS] at hd hc
  · have hj14 : 14 ≤ j := by omega
    have hp : 3^14 ≤ 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hj14
    have hx : 2548470 < 3^14 := by norm_num
    have hlt : 2548470 < 3^j := lt_of_lt_of_le hx hp
    have hd0 : gstDigitS 2548470 j = 0 := by
      unfold gstDigitS
      rw [Nat.div_eq_of_lt hlt]
      simp
    omega

/-- Concrete seed-two child suffix after its globally last Happy Gate. -/
theorem gpt56_concrete_child_suffix_bad :
    GSTSeededBadTraceS 2 9 := by
  intro j
  unfold GSTBadPairS
  intro h
  rcases h with ⟨hd, hc⟩
  by_cases hj : j < 3
  · interval_cases j <;>
      norm_num [gstDigitS, gstAffineMulCarryS] at hd hc
  · have hj3 : 3 ≤ j := by omega
    have hp : 3^3 ≤ 3^j :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) hj3
    have hx : 9 < 3^3 := by norm_num
    have hlt : 9 < 3^j := lt_of_lt_of_le hx hp
    have hd0 : gstDigitS 9 j = 0 := by
      unfold gstDigitS
      rw [Nat.div_eq_of_lt hlt]
      simp
    omega

/-- The canonical last-gate two-boundary trap is genuinely realizable.

    Parameters are the exact canonical values for `s=2,n=1`:
      A = 4^(3^2) = 262144,
      c = 9709 = 1 + 3*3236,
      T = Q_3(1) = 222399981598543.

    The child last Happy Gate is q=27.  At cut q+1=28 the retained state is
      D=0, Z=189174, W=232408, C=2, Y=9.

    Consequently any universal theorem asserting that this finite last-gate
    trap itself is impossible is too strong: the lost datum is the parent's
    earlier history.  Production must retain the complete all-depth parent
    bad hypothesis instead of reducing to this suffix-only object. -/
theorem gpt56_concrete_canonical_two_boundary_trap :
    GSTCanonicalTwoBoundaryTrapS 262144 3236 222399981598543 := by
  refine ⟨27, ?_⟩
  dsimp only
  have hD :
      gstAffineMulCarryS 4 1
        (3236 + 262144 * 222399981598543) 28 = 0 := by
    norm_num [gstAffineMulCarryS]
  have hZ :
      gstAffineMulCarryS 262144 3236 222399981598543 28 = 189174 := by
    norm_num [gstAffineMulCarryS]
  have hW :
      gstAffineMulCarryS 262144 (1 + 4*3236)
        (4*222399981598543) 28 = 232408 := by
    norm_num [gstAffineMulCarryS]
  have hC :
      gstAffineMulCarryS 4 0 222399981598543 28 = 2 := by
    norm_num [gstAffineMulCarryS]
  have hY :
      222399981598543 / 3^28 = 9 := by
    norm_num
  rw [hD, hZ, hW, hC, hY]
  refine ⟨?_, ?_, Or.inl rfl, ?_, ?_⟩
  · norm_num
    exact gpt56_concrete_parent_suffix_bad
  · exact gpt56_concrete_child_suffix_bad
  · norm_num
  · norm_num

#print axioms gpt56_concrete_canonical_two_boundary_trap
