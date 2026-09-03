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

/-- At the exact dyadic saturation boundary `k = 2*t`, the physical `x4`
    chart has no remaining dyadic condition at all.  This packages the
    boundary in the form needed by later relocation constructions. -/
theorem six_iso_mul_four_pow_at_saturation_iff_triadic
    (t : Nat) (x y : Int) :
    SixAdicIsoAt (2*t) ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      TriadicShadowAt (2*t) x y := by
  exact six_iso_mul_four_pow_iff_triadic_of_saturated (2*t) t (by rfl) x y

/-- Divisibility version of the exact saturation boundary. -/
theorem six_pow_dvd_four_pow_at_saturation_iff_triadic
    (t : Nat) (x y : Int) :
    (6 : Int)^(2*t) ∣ (4 : Int)^t*(x-y) ↔
      (3 : Int)^(2*t) ∣ x-y := by
  exact six_pow_dvd_four_pow_mul_sub_iff_triadic_of_saturated (2*t) t (by rfl) x y

/-- Consecutive positive four-powers always meet at six-adic depth one.  This
    is the exact physical pair occurring at a propagation step. -/
theorem consecutive_four_powers_six_iso_one
    (t : Nat) (ht : 1 ≤ t) :
    SixAdicIsoAt 1 ((4 : Int)^(t+1)) ((4 : Int)^t) := by
  have hkt : 1 ≤ 2*t := by omega
  have htri : TriadicShadowAt 1 (4 : Int) 1 := by
    refine ⟨1, ?_⟩
    norm_num
  have hsix : SixAdicIsoAt 1 ((4 : Int)^t * 4) ((4 : Int)^t * 1) :=
    (six_iso_mul_four_pow_iff_triadic_of_saturated 1 t hkt 4 1).2 htri
  simpa [pow_succ] using hsix

/-- The same consecutive four-power pair never reaches six-adic depth two.
    Thus the saturated six-adic contact has exact depth one; any deeper
    relocation information must come from the retained triadic coordinates,
    not from an unproved six-adic strengthening. -/
theorem consecutive_four_powers_not_six_iso_two
    (t : Nat) (ht : 1 ≤ t) :
    ¬ SixAdicIsoAt 2 ((4 : Int)^(t+1)) ((4 : Int)^t) := by
  have hkt : 2 ≤ 2*t := by omega
  intro hsix
  have hsix' : SixAdicIsoAt 2 ((4 : Int)^t * 4) ((4 : Int)^t * 1) := by
    simpa [pow_succ] using hsix
  have htri : TriadicShadowAt 2 (4 : Int) 1 :=
    (six_iso_mul_four_pow_iff_triadic_of_saturated 2 t hkt 4 1).1 hsix'
  rcases htri with ⟨q, hq⟩
  norm_num at hq
  omega

/-- Exact six-adic contact depth of consecutive positive powers of four. -/
theorem consecutive_four_powers_exact_six_depth_one
    (t : Nat) (ht : 1 ≤ t) :
    SixAdicIsoAt 1 ((4 : Int)^(t+1)) ((4 : Int)^t) ∧
      ¬ SixAdicIsoAt 2 ((4 : Int)^(t+1)) ((4 : Int)^t) := by
  exact ⟨consecutive_four_powers_six_iso_one t ht,
    consecutive_four_powers_not_six_iso_two t ht⟩

end GSTGraphV2SixAdicSaturationCollapse
