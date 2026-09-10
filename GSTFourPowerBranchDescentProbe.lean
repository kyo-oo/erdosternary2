import GSTFourPowerThirdWaveBranchReactor

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option pp.all false

namespace GSTFourPowerBranchDescentProbe

open GSTFourPowerDirectExistence
open GSTFourPowerThirdWaveBranchReactor

/-- Probe: direct exponent form of the universal third-wave theorem. -/
theorem thirdWaveNoCommonDescent_probe : ThirdWaveNoCommonDescent := by
  unfold ThirdWaveNoCommonDescent
  constructor
  · intro q hNoChild
    trace_state
    done
  · constructor
    · intro q hNoChild
      trace_state
      done
    · intro q hNoChild
      trace_state
      done

/-- Probe: original branch form, obtained immediately after the direct descent
is closed. This remains intentionally downstream of the direct exponent target. -/
theorem branchBadDescent_probe :
    GSTFourPowerUniversalInduction.BranchBadDescent := by
  exact (branchBadDescent_iff_thirdWaveNoCommonDescent).2
    thirdWaveNoCommonDescent_probe

end GSTFourPowerBranchDescentProbe
