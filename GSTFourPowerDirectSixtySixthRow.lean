import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectSixtySixthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row66_reference :
    digit3 (4 ^ 75) 66 = 2 ∧ digit3 (4 ^ 76) 66 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod30903154382632612361920641803529_75
    (N : Nat) (hN : N % 30903154382632612361920641803529 = 75) : CommonTwo N := by
  have hPow : 3 ^ 66 = 30903154382632612361920641803529 := by norm_num
  have hExp : N % 3 ^ 66 = 75 % 3 ^ 66 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (66 + 1) = 4 ^ 75 % 3 ^ (66 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 66 N 75).2 hExp
  have hd0 : digit3 (4 ^ N) 66 = 2 := by
    calc
      digit3 (4 ^ N) 66 = digit3 (4 ^ 75) 66 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row66_reference.1
  have hExp1 : (N + 1) % 3 ^ 66 = 76 % 3 ^ 66 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (66 + 1) = 4 ^ 76 % 3 ^ (66 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 66 (N + 1) 76).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 66 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 66 = digit3 (4 ^ 76) 66 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row66_reference.2
  exact ⟨66, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod30903154382632612361920641803529_75
    (N : Nat) (hN : N % 30903154382632612361920641803529 = 75) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod30903154382632612361920641803529_75 N hN)

theorem four_power_happy_propagates_of_next_mod30903154382632612361920641803529_75
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 30903154382632612361920641803529 = 75) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod30903154382632612361920641803529_75 (K + 1) hNext

#check commonTwo_of_mod30903154382632612361920641803529_75
#check physical_happy_of_mod30903154382632612361920641803529_75
#check four_power_happy_propagates_of_next_mod30903154382632612361920641803529_75

end GSTFourPowerDirectSixtySixthRow
