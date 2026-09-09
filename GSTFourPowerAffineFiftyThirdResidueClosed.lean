import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

namespace GSTFourPowerAffineFiftyThirdResidueClosed

open GSTFourPowerAffineOrbit

 theorem affineOrbit_279775_mod53_closed :
    affineOrbit 279775 % 19383245667680019896796723 = 18090587917995305367585538 := by
  have hpow := four_pow_eq_one_plus_three_affineOrbit 279775
  have hA : affineOrbit 279775 = (4^279775 - 1) / 3 := by
    omega
  rw [hA]
  norm_num

#check affineOrbit_279775_mod53_closed

end GSTFourPowerAffineFiftyThirdResidueClosed
