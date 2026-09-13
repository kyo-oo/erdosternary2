import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredTwentySecondRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row122_reference :
    digit3 (4 ^ 123) 122 = 2 ∧ digit3 (4 ^ 124) 122 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod16173092699229880893718618465586445357583280647840659957609_123
    (N : Nat) (hN : N % 16173092699229880893718618465586445357583280647840659957609 = 123) : CommonTwo N := by
  have hPow : 3 ^ 122 = 16173092699229880893718618465586445357583280647840659957609 := by norm_num
  have hExp : N % 3 ^ 122 = 123 % 3 ^ 122 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (122 + 1) = 4 ^ 123 % 3 ^ (122 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 122 N 123).2 hExp
  have hd0 : digit3 (4 ^ N) 122 = 2 := by
    calc
      digit3 (4 ^ N) 122 = digit3 (4 ^ 123) 122 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row122_reference.1
  have hExp1 : (N + 1) % 3 ^ 122 = 124 % 3 ^ 122 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (122 + 1) = 4 ^ 124 % 3 ^ (122 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 122 (N + 1) 124).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 122 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 122 = digit3 (4 ^ 124) 122 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row122_reference.2
  exact ⟨122, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod16173092699229880893718618465586445357583280647840659957609_123
    (N : Nat) (hN : N % 16173092699229880893718618465586445357583280647840659957609 = 123) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod16173092699229880893718618465586445357583280647840659957609_123 N hN)

theorem four_power_happy_propagates_of_next_mod16173092699229880893718618465586445357583280647840659957609_123
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 16173092699229880893718618465586445357583280647840659957609 = 123) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod16173092699229880893718618465586445357583280647840659957609_123 (K + 1) hNext

#check commonTwo_of_mod16173092699229880893718618465586445357583280647840659957609_123
#check physical_happy_of_mod16173092699229880893718618465586445357583280647840659957609_123
#check four_power_happy_propagates_of_next_mod16173092699229880893718618465586445357583280647840659957609_123

end GSTFourPowerDirectOneHundredTwentySecondRow
