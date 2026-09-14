import GSTFourPowerDirectTwoHundredTwentySeventhRow

namespace GSTFourPowerDirectTwoHundredThirtySeventhRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row237_reference :
    digit3 (4 ^ 238) 237 = 2 ∧ digit3 (4 ^ 239) 237 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238
    (N : Nat)
    (hN : N % 119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363 = 238) :
    CommonTwo N := by
  have hPow :
      3 ^ 237 = 119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363 := by
    norm_num
  have hExp : N % 3 ^ 237 = 238 % 3 ^ 237 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid :
      4 ^ N % 3 ^ (237 + 1) = 4 ^ 238 % 3 ^ (237 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 237 N 238).2 hExp
  have hd0 : digit3 (4 ^ N) 237 = 2 := by
    calc
      digit3 (4 ^ N) 237 = digit3 (4 ^ 238) 237 :=
        digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row237_reference.1
  have hExp1 : (N + 1) % 3 ^ 237 = 239 % 3 ^ 237 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 :
      4 ^ (N + 1) % 3 ^ (237 + 1) = 4 ^ 239 % 3 ^ (237 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 237 (N + 1) 239).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 237 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 237 = digit3 (4 ^ 239) 237 :=
        digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row237_reference.2
  exact ⟨237, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238
    (N : Nat)
    (hN : N % 119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363 = 238) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238 N hN)

theorem four_power_happy_propagates_of_next_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363 = 238) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238 (K + 1) hNext

#check commonTwo_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238
#check physical_happy_of_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238
#check four_power_happy_propagates_of_next_mod119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363_238

end GSTFourPowerDirectTwoHundredThirtySeventhRow
