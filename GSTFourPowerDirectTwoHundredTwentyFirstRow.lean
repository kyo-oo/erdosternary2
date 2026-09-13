import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerDirectHappyBridge

namespace GSTFourPowerDirectTwoHundredTwentyFirstRow

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerDirectHappyBridge

private theorem row221_reference :
    digit3 (4 ^ 222) 221 = 2 ∧ digit3 (4 ^ 223) 221 = 2 := by
  norm_num [digit3]

theorem commonTwo_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222
    (N : Nat) (hN : N % 2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203 = 222) : CommonTwo N := by
  have hPow : 3 ^ 221 = 2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203 := by norm_num
  have hExp : N % 3 ^ 221 = 222 % 3 ^ 221 := by
    rw [hPow]
    norm_num
    exact hN
  have hPowResid : 4 ^ N % 3 ^ (221 + 1) = 4 ^ 222 % 3 ^ (221 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 221 N 222).2 hExp
  have hd0 : digit3 (4 ^ N) 221 = 2 := by
    calc
      digit3 (4 ^ N) 221 = digit3 (4 ^ 222) 221 := digit3_eq_of_mod_next _ _ _ hPowResid
      _ = 2 := row221_reference.1
  have hExp1 : (N + 1) % 3 ^ 221 = 223 % 3 ^ 221 := by
    rw [Nat.add_mod, hExp]
    norm_num
  have hPowResid1 : 4 ^ (N + 1) % 3 ^ (221 + 1) = 4 ^ 223 % 3 ^ (221 + 1) :=
    (pow4_residue_eq_iff_exponent_residue_eq 221 (N + 1) 223).2 hExp1
  have hd1 : digit3 (4 ^ (N + 1)) 221 = 2 := by
    calc
      digit3 (4 ^ (N + 1)) 221 = digit3 (4 ^ 223) 221 := digit3_eq_of_mod_next _ _ _ hPowResid1
      _ = 2 := row221_reference.2
  exact ⟨221, by norm_num, hd0, hd1⟩

theorem physical_happy_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222
    (N : Nat) (hN : N % 2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203 = 222) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ N) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222 N hN)

theorem four_power_happy_propagates_of_next_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222
    (K p : Nat) (_hK : 13 ≤ K) (_hp : 1 ≤ p)
    (_hHappy : GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ K) p)
      (GSTCanonicalTailStateIso.digit3 (4 ^ K) p))
    (hNext : (K + 1) % 2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203 = 222) :
    ∃ q : Nat, 1 ≤ q ∧ GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4 ^ (K + 1)) q)
      (GSTCanonicalTailStateIso.digit3 (4 ^ (K + 1)) q) := by
  exact physical_happy_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222 (K + 1) hNext

#check commonTwo_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222
#check physical_happy_of_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222
#check four_power_happy_propagates_of_next_mod2778416139299363012879807394073541900105316880497683964790215807591118587512684646756204117659106898285203_222

end GSTFourPowerDirectTwoHundredTwentyFirstRow
