import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredEighthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row208_reference :
    digit3 (4 ^ 209) 208 = 2 ∧ digit3 (4 ^ 210) 208 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209
    (N : Nat) (hN : N % 1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561 = 209) : CommonTwo N := by
  have hPow : 3 ^ 208 = 1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561 := by norm_num
  have hExp : N % 3 ^ 208 = 209 % 3 ^ 208 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (208 + 1) = 4 ^ 209 % 3 ^ (208 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 208 N 209).2 hExp
  have hd0 : digit3 (4 ^ N) 208 = 2 := by
    calc
      digit3 (4 ^ N) 208 = digit3 (4 ^ 209) 208 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row208_reference.1
  have hExp1 : (N + 1) % 3 ^ 208 = 210 % 3 ^ 208 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (208 + 1) = 4 ^ 210 % 3 ^ (208 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 208 (N + 1) 210).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 208 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 208 = digit3 (4 ^ 210) 208 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row208_reference.2
  exact ⟨208, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209
    (N : Nat) (hN : N % 1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561 = 209) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209 N hN)

theorem four_power_happy_propagates_of_next_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561 = 209) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209 (K + 1) hNext

#check commonTwo_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209
#check physical_happy_of_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209
#check four_power_happy_propagates_of_next_mod1742693381014614361631744253876750131626600682858921288089186323970185832803443622626158010427690561_209

end GSTFourPowerDirectTwoHundredEighthRow
