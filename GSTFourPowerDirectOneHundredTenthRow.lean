import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectOneHundredTenthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row110_reference :
    digit3 (4 ^ 111) 110 = 2 ∧ digit3 (4 ^ 112) 110 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod30432527221704537086371993251530170531786747066637049_111
    (N : Nat) (hN : N % 30432527221704537086371993251530170531786747066637049 = 111) : CommonTwo N := by
  have hPow : 3 ^ 110 = 30432527221704537086371993251530170531786747066637049 := by norm_num
  have hExp : N % 3 ^ 110 = 111 % 3 ^ 110 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (110 + 1) = 4 ^ 111 % 3 ^ (110 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 110 N 111).2 hExp
  have hd0 : digit3 (4 ^ N) 110 = 2 := by
    calc
      digit3 (4 ^ N) 110 = digit3 (4 ^ 111) 110 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row110_reference.1
  have hExp1 : (N + 1) % 3 ^ 110 = 112 % 3 ^ 110 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (110 + 1) = 4 ^ 112 % 3 ^ (110 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 110 (N + 1) 112).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 110 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 110 = digit3 (4 ^ 112) 110 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row110_reference.2
  exact ⟨110, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod30432527221704537086371993251530170531786747066637049_111
    (N : Nat) (hN : N % 30432527221704537086371993251530170531786747066637049 = 111) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod30432527221704537086371993251530170531786747066637049_111 N hN)

theorem four_power_happy_propagates_of_next_mod30432527221704537086371993251530170531786747066637049_111
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 30432527221704537086371993251530170531786747066637049 = 111) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod30432527221704537086371993251530170531786747066637049_111 (K + 1) hNext

#check commonTwo_of_mod30432527221704537086371993251530170531786747066637049_111
#check physical_happy_of_mod30432527221704537086371993251530170531786747066637049_111
#check four_power_happy_propagates_of_next_mod30432527221704537086371993251530170531786747066637049_111

end GSTFourPowerDirectOneHundredTenthRow
