import GSTFourPowerAffineOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

namespace GSTFourPowerAffineFiftyThirdResidueClosed

open GSTFourPowerAffineOrbit

private theorem one_plus_three_mul_mod (a m : Nat) (hm : 0 < m) :
    (1 + 3 * a) % (3 * m) = 1 + 3 * (a % m) := by
  have hlt : a % m < m := Nat.mod_lt _ hm
  have hsplit : a % m + m * (a / m) = a := Nat.mod_add_div a m
  rw [← hsplit]
  have hrearr :
      1 + 3 * (a % m + m * (a / m)) =
        (1 + 3 * (a % m)) + (3 * m) * (a / m) := by
    ring
  rw [hrearr]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (by omega : 1 + 3 * (a % m) < 3 * m)]

theorem affineOrbit_279775_mod53_closed :
    affineOrbit 279775 % 19383245667680019896796723 = 18090587917995305367585538 := by
  have hpow := four_pow_eq_one_plus_three_affineOrbit 279775
  have hPowMod :
      4^279775 % 58149737003040059690390169 = 54271763753985916102756615 := by
    norm_num
  rw [hpow] at hPowMod
  have hmod := one_plus_three_mul_mod (affineOrbit 279775) 19383245667680019896796723 (by norm_num)
  norm_num at hmod
  rw [hmod] at hPowMod
  omega

#check affineOrbit_279775_mod53_closed

end GSTFourPowerAffineFiftyThirdResidueClosed
