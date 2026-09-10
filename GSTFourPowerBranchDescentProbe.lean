import GSTFourPowerUniversalInduction

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option pp.all false

namespace GSTFourPowerBranchDescentProbe

open GSTFourPowerUniversalInduction
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineRenormalizedOrbit

/-- Probe: the exact universal theorem that would make the axiom replacement unconditional. -/
theorem branchBadDescent_probe : BranchBadDescent := by
  unfold BranchBadDescent
  constructor
  · intro q hBad
    trace_state
    done
  · constructor
    · intro q hBad
      trace_state
      done
    · intro q hBad
      trace_state
      done

end GSTFourPowerBranchDescentProbe
