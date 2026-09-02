import GSTGraphV2FourPowerRelocation
import GSTInfiniteFourPowerNavigation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocationClosure

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-- Universal Graph-V2 relocation.  The repaired four-power navigation theorem
is stronger than the requested induction edge: for every exponent at least
8 it constructs a physical Happy row directly, so at `K+1` it supplies the
required relocated witness independently of the source row. -/
theorem four_power_happy_propagates :
    GSTGraphV2FourPowerRelocation.FourPowerHappyPropagation := by
  intro K p hK hp hHappy
  obtain ⟨q, hq3, hqHappy⟩ :=
    GSTInfiniteFourPowerNavigation.four_power_happy_ge_three (K+1) (by omega)
  refine ⟨q, by omega, ?_⟩
  simpa [graph, cell, GSTCanonicalSevenAxisBridge.vertex] using hqHappy

#check four_power_happy_propagates
#print axioms GSTInfiniteFourPowerNavigation.power_three_step_collision
#print axioms GSTInfiniteFourPowerNavigation.four_power_happy_ge_three
#print axioms four_power_happy_propagates

end GSTGraphV2FourPowerRelocationClosure
