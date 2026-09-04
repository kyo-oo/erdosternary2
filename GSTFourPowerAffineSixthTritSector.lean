import GSTFourPowerAffineSixthTrit

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineSixthTritSector

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

/-- Exact sixth-prefix transfer specialized to exponent residue `486 mod 729`. -/
private theorem affineOrbit_mod729_eq_486_of_exponent
    (N : Nat) (hN : N % 729 = 486) :
    affineOrbit N % 729 = 486 := by
  have h := (affineOrbit_residue_eq_iff_exponent_residue_eq 6 N 486).2 (by
    simpa using hN)
  norm_num [affineOrbit] at h ⊢
  exact h

/-- Fresh sixth-trit kill pattern.  The affine prefix `000002` (least
significant trit first) forces a hypothetical bad channel through
`1 -> 0 -> 0 -> 0 -> 0 -> 0`; state `0` cannot survive the terminal trit
`2`. -/
private theorem commonTwo_of_mod729_pattern_000002
    (N : Nat) (hAmod : affineOrbit N % 729 = 486) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hd0 : lowDigit A = 0 := by unfold lowDigit; dsimp [A]; omega
  have hd1 : lowDigit (tail3 A) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd3 : lowDigit (tail3 (tail3 (tail3 A))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd4 : lowDigit (tail3 (tail3 (tail3 (tail3 A)))) = 0 := by unfold lowDigit tail3; dsimp [A]; omega
  have hd5 : lowDigit (tail3 (tail3 (tail3 (tail3 (tail3 A))))) = 2 := by unfold lowDigit tail3; dsimp [A]; omega
  have hbad0 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad1 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad0
    simpa using hbad0
  have hbad2 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad1
    simpa using hbad1
  have hbad3 : BadChannel 0 (tail3 (tail3 (tail3 A))) := by
    rw [badChannel_zero_iff, hd2] at hbad2
    simpa using hbad2
  have hbad4 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 A)))) := by
    rw [badChannel_zero_iff, hd3] at hbad3
    simpa using hbad3
  have hbad5 : BadChannel 0 (tail3 (tail3 (tail3 (tail3 (tail3 A))))) := by
    rw [badChannel_zero_iff, hd4] at hbad4
    simpa using hbad4
  rw [badChannel_zero_iff, hd5] at hbad5
  simpa using hbad5

/-- Exponent residue `486 mod 729` has an actual common-two coordinate. -/
theorem commonTwo_of_mod729_fourEightSix
    (N : Nat) (hN : N % 729 = 486) : CommonTwo N := by
  exact commonTwo_of_mod729_pattern_000002 N
    (affineOrbit_mod729_eq_486_of_exponent N hN)

/-- Convert the new sixth-trit kill directly into a physical Happy row. -/
theorem physical_happy_of_mod729_fourEightSix
    (N : Nat) (hN : N % 729 = 486) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  exact commonTwo_to_physical_happy_row N
    (commonTwo_of_mod729_fourEightSix N hN)

/-- Task-3.3-shaped direct relocation constructor for next-sheet residue `486`.
The source Happy row is not transported; a fresh physical row is constructed
on `4^(K+1)`. -/
theorem four_power_happy_propagates_of_next_mod729_fourEightSix
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 729 = 486) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod729_fourEightSix (K+1) hNext

#check commonTwo_of_mod729_fourEightSix
#check physical_happy_of_mod729_fourEightSix
#check four_power_happy_propagates_of_next_mod729_fourEightSix
#print axioms commonTwo_of_mod729_fourEightSix
#print axioms physical_happy_of_mod729_fourEightSix
#print axioms four_power_happy_propagates_of_next_mod729_fourEightSix

end GSTFourPowerAffineSixthTritSector
