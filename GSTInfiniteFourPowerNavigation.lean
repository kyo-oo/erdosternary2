import GSTTactic
import GSTGraphV2SixAdicSynchronizedShadows

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteFourPowerNavigation

open GSTGraphV2SixAdicSynchronizedShadows

/-- Public bridge surface for the green six-adic skew theorem used by the
four-power surgery line.  This file deliberately exposes only the transparent
six-adic bridge layer and does not resurrect the obsolete collision/descent
`False` seam. -/
theorem four_power_six_adic_skew_bridge
    (k t : Nat) (x y : Int) :
    (6 : Int)^k ∣ (4 : Int)^t*(x-y) ↔
      (3 : Int)^k ∣ x-y ∧ (2 : Int)^(k-2*t) ∣ x-y := by
  exact six_pow_dvd_four_pow_mul_sub_iff_truncated k t x y

/-- Dyadic branch of the same bridge, including the saturated case. -/
theorem four_power_dyadic_shadow_bridge
    (k t : Nat) (x y : Int) :
    GSTGraphV2SixAdicOntologicalGeometry.DyadicShadowAt k
        ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      GSTGraphV2SixAdicOntologicalGeometry.DyadicShadowAt (k-2*t) x y := by
  exact dyadic_shadow_mul_four_pow_iff_truncated k t x y

/-- Triadic branch of the same bridge: multiplying by a power of four preserves
all triadic shadow depth. -/
theorem four_power_triadic_shadow_bridge
    (k t : Nat) (x y : Int) :
    GSTGraphV2SixAdicOntologicalGeometry.TriadicShadowAt k
        ((4 : Int)^t*x) ((4 : Int)^t*y) ↔
      GSTGraphV2SixAdicOntologicalGeometry.TriadicShadowAt k x y := by
  exact triadic_shadow_mul_four_pow_iff k t x y

#check four_power_six_adic_skew_bridge
#check four_power_dyadic_shadow_bridge
#check four_power_triadic_shadow_bridge
#print axioms four_power_six_adic_skew_bridge
#print axioms four_power_dyadic_shadow_bridge
#print axioms four_power_triadic_shadow_bridge

end GSTInfiniteFourPowerNavigation
