import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectNinetyEighthRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row98_reference :
    digit3 (4 ^ 99) 98 = 2 ∧ digit3 (4 ^ 100) 98 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod57264168970223481226273458862846808078011946889_99
    (N : Nat) (hN : N % 57264168970223481226273458862846808078011946889 = 99) : CommonTwo N := by
  have hPow : 3 ^ 98 = 57264168970223481226273458862846808078011946889 := by norm_num
  have hExp : N % 3 ^ 98 = 99 % 3 ^ 98 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (98 + 1) = 4 ^ 99 % 3 ^ (98 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 98 N 99).2 hExp
  have hd0 : digit3 (4 ^ N) 98 = 2 := by
    calc
      digit3 (4 ^ N) 98 = digit3 (4 ^ 99) 98 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row98_reference.1
  have hExp1 : (N + 1) % 3 ^ 98 = 100 % 3 ^ 98 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (98 + 1) = 4 ^ 100 % 3 ^ (98 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 98 (N + 1) 100).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 98 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 98 = digit3 (4 ^ 100) 98 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row98_reference.2
  exact ⟨98, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod57264168970223481226273458862846808078011946889_99
    (N : Nat) (hN : N % 57264168970223481226273458862846808078011946889 = 99) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod57264168970223481226273458862846808078011946889_99 N hN)

theorem four_power_happy_propagates_of_next_mod57264168970223481226273458862846808078011946889_99
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 57264168970223481226273458862846808078011946889 = 99) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod57264168970223481226273458862846808078011946889_99 (K + 1) hNext

#check commonTwo_of_mod57264168970223481226273458862846808078011946889_99
#check physical_happy_of_mod57264168970223481226273458862846808078011946889_99
#check four_power_happy_propagates_of_next_mod57264168970223481226273458862846808078011946889_99

end GSTFourPowerDirectNinetyEighthRow
