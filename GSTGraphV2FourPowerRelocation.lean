import GSTGraphV2NonlocalCascade
import GSTGraphV2CanonicalEscape
import GSTGraphV2CanonicalInfiniteCycle

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2FourPowerRelocation

open GSTCanonicalTailStateIso
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTGraphV2NonlocalCascade

/-- Exact universal induction edge to be proved without weakening.

A physical Happy cell on the `4^K` unit sheet must force the existence of
some physical Happy cell on the `4^(K+1)` sheet.  The relocated row is not
assumed to be local to the input row. -/
def FourPowerHappyPropagation : Prop :=
  ∀ K p : Nat, 8 ≤ K → 1 ≤ p →
    HappyCell (graph 1 K p).seven.carry (graph 1 K p).seven.digit →
    ∃ q : Nat, 1 ≤ q ∧
      HappyCell (graph 1 (K+1) q).seven.carry
        (graph 1 (K+1) q).seven.digit

#check FourPowerHappyPropagation

end GSTGraphV2FourPowerRelocation
