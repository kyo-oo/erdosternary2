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
  simp [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 + 3 * (a % m) < 3 * m)]

private theorem pow4_279775_mod54 :
    4^279775 % 58149737003040059690390169 = 54271763753985916102756615 := by
  have hp0 : 4^1 % 58149737003040059690390169 = 4 := by norm_num
  have hp1 : 4^2 % 58149737003040059690390169 = 16 := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, pow_add, Nat.mul_mod, hp0, hp0]
    norm_num
  have hp2 : 4^4 % 58149737003040059690390169 = 256 := by
    rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add, Nat.mul_mod, hp1, hp1]
    norm_num
  have hp3 : 4^8 % 58149737003040059690390169 = 65536 := by
    rw [show (8 : Nat) = 4 + 4 by norm_num, pow_add, Nat.mul_mod, hp2, hp2]
    norm_num
  have hp4 : 4^16 % 58149737003040059690390169 = 4294967296 := by
    rw [show (16 : Nat) = 8 + 8 by norm_num, pow_add, Nat.mul_mod, hp3, hp3]
    norm_num
  have hp5 : 4^32 % 58149737003040059690390169 = 18446744073709551616 := by
    rw [show (32 : Nat) = 16 + 16 by norm_num, pow_add, Nat.mul_mod, hp4, hp4]
    norm_num
  have hp6 : 4^64 % 58149737003040059690390169 = 11110987165577286350885494 := by
    rw [show (64 : Nat) = 32 + 32 by norm_num, pow_add, Nat.mul_mod, hp5, hp5]
    norm_num
  have hp7 : 4^128 % 58149737003040059690390169 = 48359171654944081050312718 := by
    rw [show (128 : Nat) = 64 + 64 by norm_num, pow_add, Nat.mul_mod, hp6, hp6]
    norm_num
  have hp8 : 4^256 % 58149737003040059690390169 = 866926062626251569075796 := by
    rw [show (256 : Nat) = 128 + 128 by norm_num, pow_add, Nat.mul_mod, hp7, hp7]
    norm_num
  have hp9 : 4^512 % 58149737003040059690390169 = 53213196969798908643648331 := by
    rw [show (512 : Nat) = 256 + 256 by norm_num, pow_add, Nat.mul_mod, hp8, hp8]
    norm_num
  have hp10 : 4^1024 % 58149737003040059690390169 = 48587610030428679805699321 := by
    rw [show (1024 : Nat) = 512 + 512 by norm_num, pow_add, Nat.mul_mod, hp9, hp9]
    norm_num
  have hp11 : 4^2048 % 58149737003040059690390169 = 19437331142939988218371792 := by
    rw [show (2048 : Nat) = 1024 + 1024 by norm_num, pow_add, Nat.mul_mod, hp10, hp10]
    norm_num
  have hp12 : 4^4096 % 58149737003040059690390169 = 46994542563393086660076532 := by
    rw [show (4096 : Nat) = 2048 + 2048 by norm_num, pow_add, Nat.mul_mod, hp11, hp11]
    norm_num
  have hp13 : 4^8192 % 58149737003040059690390169 = 43662798615577007775148576 := by
    rw [show (8192 : Nat) = 4096 + 4096 by norm_num, pow_add, Nat.mul_mod, hp12, hp12]
    norm_num
  have hp14 : 4^16384 % 58149737003040059690390169 = 9424853133929994860242591 := by
    rw [show (16384 : Nat) = 8192 + 8192 by norm_num, pow_add, Nat.mul_mod, hp13, hp13]
    norm_num
  have hp15 : 4^32768 % 58149737003040059690390169 = 55309892918356031316180784 := by
    rw [show (32768 : Nat) = 16384 + 16384 by norm_num, pow_add, Nat.mul_mod, hp14, hp14]
    norm_num
  have hp16 : 4^65536 % 58149737003040059690390169 = 7398682165494073884235432 := by
    rw [show (65536 : Nat) = 32768 + 32768 by norm_num, pow_add, Nat.mul_mod, hp15, hp15]
    norm_num
  have hp17 : 4^131072 % 58149737003040059690390169 = 44702502467311701228320935 := by
    rw [show (131072 : Nat) = 65536 + 65536 by norm_num, pow_add, Nat.mul_mod, hp16, hp16]
    norm_num
  have hp18 : 4^262144 % 58149737003040059690390169 = 30829734325007268597976477 := by
    rw [show (262144 : Nat) = 131072 + 131072 by norm_num, pow_add, Nat.mul_mod, hp17, hp17]
    norm_num
  have hc1 : 4^1 % 58149737003040059690390169 = 4 := hp0
  have hc3 : 4^3 % 58149737003040059690390169 = 64 := by
    rw [show (3 : Nat) = 1 + 2 by norm_num, pow_add, Nat.mul_mod, hc1, hp1]
    norm_num
  have hc7 : 4^7 % 58149737003040059690390169 = 16384 := by
    rw [show (7 : Nat) = 3 + 4 by norm_num, pow_add, Nat.mul_mod, hc3, hp2]
    norm_num
  have hc15 : 4^15 % 58149737003040059690390169 = 1073741824 := by
    rw [show (15 : Nat) = 7 + 8 by norm_num, pow_add, Nat.mul_mod, hc7, hp3]
    norm_num
  have hc31 : 4^31 % 58149737003040059690390169 = 4611686018427387904 := by
    rw [show (31 : Nat) = 15 + 16 by norm_num, pow_add, Nat.mul_mod, hc15, hp4]
    norm_num
  have hc95 : 4^95 % 58149737003040059690390169 = 50259412604447781819023005 := by
    rw [show (95 : Nat) = 31 + 64 by norm_num, pow_add, Nat.mul_mod, hc31, hp6]
    norm_num
  have hc223 : 4^223 % 58149737003040059690390169 = 6335720281376086933923817 := by
    rw [show (223 : Nat) = 95 + 128 by norm_num, pow_add, Nat.mul_mod, hc95, hp7]
    norm_num
  have hc1247 : 4^1247 % 58149737003040059690390169 = 50396403396738620431189177 := by
    rw [show (1247 : Nat) = 223 + 1024 by norm_num, pow_add, Nat.mul_mod, hc223, hp10]
    norm_num
  have hc17631 : 4^17631 % 58149737003040059690390169 = 40095417087015570559734265 := by
    rw [show (17631 : Nat) = 1247 + 16384 by norm_num, pow_add, Nat.mul_mod, hc1247, hp14]
    norm_num
  have hc279775 : 4^279775 % 58149737003040059690390169 = 54271763753985916102756615 := by
    rw [show (279775 : Nat) = 17631 + 262144 by norm_num, pow_add, Nat.mul_mod, hc17631, hp18]
    norm_num
  exact hc279775

theorem affineOrbit_279775_mod53_closed :
    affineOrbit 279775 % 19383245667680019896796723 = 18090587917995305367585538 := by
  have hpow := four_pow_eq_one_plus_three_affineOrbit 279775
  have hPowMod := pow4_279775_mod54
  rw [hpow] at hPowMod
  have hmod := one_plus_three_mul_mod (affineOrbit 279775) 19383245667680019896796723 (by norm_num)
  have hM : 3 * 19383245667680019896796723 = 58149737003040059690390169 := by norm_num
  rw [hM] at hmod
  rw [hmod] at hPowMod
  omega

#check affineOrbit_279775_mod53_closed

end GSTFourPowerAffineFiftyThirdResidueClosed
