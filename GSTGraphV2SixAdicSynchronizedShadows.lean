import GSTGraphV2SixAdicOntologicalGeometryLaws

/-!
# Synchronized Dyadic–Triadic Characterization

This file strengthens the GST six-adic overlay by proving that six-adic
resolution is exactly the simultaneous dyadic and triadic resolution at the
same depth.  This is the CRT-style synchronization theorem behind the
composite-base geometry.
-/

namespace GSTGraphV2SixAdicSynchronizedShadows

open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicOntologicalGeometryLaws

/-- Simultaneous dyadic and triadic resolution reconstructs the six-adic
    resolution at exactly the same depth. -/
theorem dyadic_triadic_to_six
    {k : Nat} {x y : Int}
    (h2 : DyadicShadowAt k x y)
    (h3 : TriadicShadowAt k x y) :
    SixAdicIsoAt k x y := by
  rcases h2 with ⟨q2, hq2⟩
  rcases h3 with ⟨q3, hq3⟩
  have hd2 : (2 : Int)^k ∣ x - y := ⟨q2, hq2⟩
  have hd3 : (3 : Int)^k ∣ x - y := ⟨q3, hq3⟩
  have hbase : IsCoprime (2 : Int) (3 : Int) :=
    Nat.Coprime.isCoprime (by decide : Nat.Coprime 2 3)
  have hcop : IsCoprime ((2 : Int)^k) ((3 : Int)^k) := by
    exact hbase.pow
  have hmul : ((2 : Int)^k * (3 : Int)^k) ∣ x - y :=
    IsCoprime.mul_dvd hcop hd2 hd3
  rcases hmul with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    x - y = ((2 : Int)^k * (3 : Int)^k) * q := hq
    _ = (6 : Int)^k * q := by
      rw [← mul_pow]
      norm_num

/-- Six-adic resolution is exactly synchronized dyadic and triadic
    resolution. -/
theorem six_iso_iff_synchronized_shadows
    {k : Nat} {x y : Int} :
    SixAdicIsoAt k x y ↔
      DyadicShadowAt k x y ∧ TriadicShadowAt k x y := by
  constructor
  · intro h
    exact ⟨six_iso_to_dyadic h, six_iso_to_triadic h⟩
  · rintro ⟨h2, h3⟩
    exact dyadic_triadic_to_six h2 h3

/-- The six-adic ball is exactly the intersection of its synchronized dyadic
    and triadic shadow balls at the same resolution. -/
theorem six_ball_membership_iff_shadows
    {k : Nat} {c x : Int} :
    x ∈ SixAdicBall k c ↔
      DyadicShadowAt k x c ∧ TriadicShadowAt k x c := by
  exact six_iso_iff_synchronized_shadows


/-! ## Exact skew action of the physical x4 chart -/

/-- Multiplication by `4^t` is a genuine isometry of every triadic shadow.
    This is the odd-prime half of the physical chart: four is a unit modulo
    every power of three. -/
theorem triadic_shadow_mul_four_pow_iff
    (k t : Nat) (x y : Int) :
    TriadicShadowAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
      TriadicShadowAt k x y := by
  constructor
  · rintro ⟨q, hq⟩
    change (3 : Int)^k ∣ x-y
    have hdiv : (3 : Int)^k ∣ (4 : Int)^t * (x-y) := by
      refine ⟨q, ?_⟩
      calc
        (4 : Int)^t * (x-y) =
            (4 : Int)^t*x - (4 : Int)^t*y := by ring
        _ = (3 : Int)^k * q := hq
    have hcop : IsCoprime ((3 : Int)^k) ((4 : Int)^t) :=
      (by norm_num : IsCoprime (3 : Int) 4).pow
    exact hcop.dvd_of_dvd_mul_left hdiv
  · rintro ⟨q, hq⟩
    refine ⟨(4 : Int)^t*q, ?_⟩
    calc
      (4 : Int)^t*x - (4 : Int)^t*y = (4 : Int)^t*(x-y) := by ring
      _ = (4 : Int)^t*((3 : Int)^k*q) := by rw [hq]
      _ = (3 : Int)^k*((4 : Int)^t*q) := by ring

/-- Below the dyadic saturation point, multiplication by `4^t = 2^(2t)`
    shifts dyadic resolution by exactly `2t`, in both directions. -/
theorem dyadic_shadow_mul_four_pow_iff
    (k t : Nat) (hkt : 2*t ≤ k) (x y : Int) :
    DyadicShadowAt k ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      DyadicShadowAt (k-2*t) x y := by
  have hk : 2*t + (k-2*t) = k := Nat.add_sub_of_le hkt
  have h4 : (4 : Int)^t = (2 : Int)^(2*t) := by
    calc
      (4 : Int)^t = ((2 : Int)^2)^t := by norm_num
      _ = (2 : Int)^(2*t) := by rw [pow_mul]
  have hpow : (2 : Int)^k =
      (2 : Int)^(2*t) * (2 : Int)^(k-2*t) := by
    rw [← hk, pow_add]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    have hc : (2 : Int)^(2*t)*(x-y) =
        (2 : Int)^(2*t)*((2 : Int)^(k-2*t)*q) := by
      calc
        (2 : Int)^(2*t)*(x-y) =
            (4 : Int)^t*x - (4 : Int)^t*y := by rw [h4]; ring
        _ = (2 : Int)^k*q := hq
        _ = (2 : Int)^(2*t)*((2 : Int)^(k-2*t)*q) := by
          rw [hpow]
          ring
    exact mul_left_cancel₀ (by positivity : (2 : Int)^(2*t) ≠ 0) hc
  · rintro ⟨q, hq⟩
    refine ⟨q, ?_⟩
    calc
      (4 : Int)^t*x - (4 : Int)^t*y =
          (2 : Int)^(2*t)*(x-y) := by rw [h4]; ring
      _ = (2 : Int)^(2*t)*((2 : Int)^(k-2*t)*q) := by rw [hq]
      _ = (2 : Int)^k*q := by rw [hpow]; ring

/-- Exact six-adic information retained by the physical x4 chart before
    dyadic saturation: full triadic depth and dyadic depth reduced by `2t`. -/
theorem six_iso_mul_four_pow_iff_skew_shadows
    (k t : Nat) (hkt : 2*t ≤ k) (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      DyadicShadowAt (k-2*t) x y ∧ TriadicShadowAt k x y := by
  rw [six_iso_iff_synchronized_shadows,
    dyadic_shadow_mul_four_pow_iff k t hkt x y,
    triadic_shadow_mul_four_pow_iff k t x y]


end GSTGraphV2SixAdicSynchronizedShadows
