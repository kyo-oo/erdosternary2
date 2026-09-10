import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectFiftySixthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row56_reference :
    digit3 (4 ^ 73) 56 = 2 ∧ digit3 (4 ^ 74) 56 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod523347633027360537213511521_73
    (N : Nat) (hN : N % 523347633027360537213511521 = 73) : CommonTwo N := by
  have hPow : 3 ^ 56 = 523347633027360537213511521 := by norm_num
  have hExp : N % 3 ^ 56 = 73 % 3 ^ 56 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (56 + 1) = 4 ^ 73 % 3 ^ (56 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 56 N 73).2 hExp
  have hd0 : digit3 (4 ^ N) 56 = 2 := by
    calc
      digit3 (4 ^ N) 56 = digit3 (4 ^ 73) 56 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row56_reference.1
  have hExp1 : (N + 1) % 3 ^ 56 = 74 % 3 ^ 56 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (56 + 1) = 4 ^ 74 % 3 ^ (56 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 56 (N + 1) 74).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 56 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 56 = digit3 (4 ^ 74) 56 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row56_reference.2
  exact ⟨56, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod523347633027360537213511521_73
    (N : Nat) (hN : N % 523347633027360537213511521 = 73) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod523347633027360537213511521_73 N hN)

theorem four_power_happy_propagates_of_next_mod523347633027360537213511521_73
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 523347633027360537213511521 = 73) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod523347633027360537213511521_73 (K + 1) hNext

#check commonTwo_of_mod523347633027360537213511521_73
#check physical_happy_of_mod523347633027360537213511521_73
#check four_power_happy_propagates_of_next_mod523347633027360537213511521_73

end GSTFourPowerDirectFiftySixthRow
