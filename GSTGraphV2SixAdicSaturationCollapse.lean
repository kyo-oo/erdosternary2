import GSTGraphV2SixAdicSynchronizedShadows

/-!
# Saturated six-adic collapse for the physical x4 chart

On the fresh six-adic production route, once `4^t` supplies all dyadic
resolution demanded at depth `k`, the six-adic condition has exactly one
remaining obstruction: the depth-`k` triadic shadow.  These are direct
corollaries of the synchronized-shadow law; no navigation or existence
principle is used.
-/

namespace GSTGraphV2SixAdicSaturationCollapse

open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicOntologicalGeometryLaws
open GSTGraphV2SixAdicSynchronizedShadows

/-- In the dyadically saturated regime, six-adic equality of the physical
    `x4` images is equivalent to the unchanged triadic shadow alone. -/
theorem six_iso_mul_four_pow_iff_triadic_of_saturated
    (k t : Nat) (hkt : k ≤ 2*t) (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      TriadicShadowAt k x y := by
  have hsub : k - 2*t = 0 := Nat.sub_eq_zero_of_le hkt
  constructor
  · intro hsix
    exact (six_iso_mul_four_pow_iff_truncated_skew_shadows k t x y).mp hsix |>.2
  · intro h3
    apply (six_iso_mul_four_pow_iff_truncated_skew_shadows k t x y).mpr
    constructor
    · rw [hsub]
      exact dyadic_shadow_zero x y
    · exact h3

/-- Divisibility form of the saturated collapse: after multiplication by
    `4^t`, divisibility by `6^k` is controlled exactly by divisibility by
    `3^k` once `k ≤ 2*t`. -/
theorem six_pow_dvd_four_pow_mul_sub_iff_triadic_of_saturated
    (k t : Nat) (hkt : k ≤ 2*t) (x y : Int) :
    (6 : Int)^k ∣ (4 : Int)^t*(x-y) ↔
      (3 : Int)^k ∣ x-y := by
  have hsub : k - 2*t = 0 := Nat.sub_eq_zero_of_le hkt
  constructor
  · intro h6
    exact (six_pow_dvd_four_pow_mul_sub_iff_truncated k t x y).mp h6 |>.1
  · intro h3
    apply (six_pow_dvd_four_pow_mul_sub_iff_truncated k t x y).mpr
    constructor
    · exact h3
    · rw [hsub]
      simp

end GSTGraphV2SixAdicSaturationCollapse
