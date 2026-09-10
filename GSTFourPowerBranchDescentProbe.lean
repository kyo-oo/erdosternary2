import GSTFourPowerThirdWaveBranchReactor

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000
set_option pp.all false

namespace GSTFourPowerBranchDescentProbe

open GSTFourPowerDirectExistence
open GSTFourPowerThirdWaveBranchReactor

/-- Probe: positive common-two propagation form of the universal third-wave theorem. -/
theorem thirdWaveCommonLift_probe : ThirdWaveCommonLift := by
  unfold ThirdWaveCommonLift
  constructor
  · intro q hCommon
    trace_state
    done
  · constructor
    · intro q hCommon
      trace_state
      done
    · intro q hCommon
      trace_state
      done

/-- Probe: direct no-common form, obtained by contrapositive duality once the
positive common-lift target is closed. -/
theorem thirdWaveNoCommonDescent_probe : ThirdWaveNoCommonDescent := by
  exact (thirdWaveNoCommonDescent_iff_commonLift).2 thirdWaveCommonLift_probe

/-- Probe: original branch form, obtained immediately after the direct descent
is closed. This remains intentionally downstream of the positive lift target. -/
theorem branchBadDescent_probe :
    GSTFourPowerUniversalInduction.BranchBadDescent := by
  exact (branchBadDescent_iff_thirdWaveNoCommonDescent).2
    thirdWaveNoCommonDescent_probe

end GSTFourPowerBranchDescentProbe
