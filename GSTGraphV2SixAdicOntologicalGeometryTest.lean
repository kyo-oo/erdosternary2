import GSTGraphV2SixAdicSynchronizedShadows

namespace GSTGraphV2SixAdicOntologicalGeometryTest

open GSTGraphV2NonEuclidean
open GSTGraphV2SixAdicOntologicalGeometry
open GSTGraphV2SixAdicOntologicalGeometryLaws
open GSTGraphV2SixAdicSynchronizedShadows

example (k : Nat) (x : Int) : SixAdicIsoAt k x x :=
  six_iso_refl k x

example (k : Nat) (x y z : Int)
    (hxy : SixAdicIsoAt k x y) (hyz : SixAdicIsoAt k y z) :
    SixAdicIsoAt k x z :=
  six_iso_nonarchimedean hxy hyz

example (k : Nat) (c : Int) (j : Fin 6) :
    sixChildCenter k c j ∈ SixAdicBall k c :=
  six_child_center_in_parent k c j

example (k : Nat) (c : Int) :
    Function.Injective (sixChildCenter k c) :=
  six_child_centers_injective k c

example (k t E F : Nat)
    (h : SixAdicIsoAt k (E : Int) (F : Int)) :
    SixAdicIsoAt k ((4 : Int)^t * E) ((4 : Int)^t * F) :=
  x4_chart_preserves_six_iso k t E F h

example (k t : Nat) (x y : Int) :
    TriadicShadowAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
      TriadicShadowAt k x y :=
  triadic_shadow_mul_four_pow_iff k t x y

example (k t : Nat) (hkt : 2 * t ≤ k) (x y : Int) :
    DyadicShadowAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
      DyadicShadowAt (k - 2 * t) x y :=
  dyadic_shadow_mul_four_pow_iff k t hkt x y

example (k t : Nat) (hkt : 2 * t ≤ k) (x y : Int) :
    SixAdicIsoAt k ((4 : Int)^t * x) ((4 : Int)^t * y) ↔
      DyadicShadowAt (k - 2 * t) x y ∧ TriadicShadowAt k x y :=
  six_iso_mul_four_pow_iff_skew_shadows k t hkt x y

#check SixAdicIsoAt
#check SixAdicBall
#check GraphIsoAt
#check six_iso_to_dyadic
#check six_iso_to_triadic
#check intersecting_equal_radius_balls_eq
#check resolved_vertex_axes_exact
#check physical_projection_iso_exact

end GSTGraphV2SixAdicOntologicalGeometryTest
