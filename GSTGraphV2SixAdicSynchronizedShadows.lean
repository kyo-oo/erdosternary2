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

end GSTGraphV2SixAdicSynchronizedShadows
