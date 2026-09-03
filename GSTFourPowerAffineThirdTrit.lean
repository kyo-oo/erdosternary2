import GSTFourPowerAffinePrefixIsometry
import GSTFourPowerAffineClassifierBridge
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineThirdTrit

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffinePrefixIsometry
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerDirectHappyBridge

private theorem affineOrbit_mod27_eq_18_of_exponent
    {N : Nat} (hN : N % 27 = 18) : affineOrbit N % 27 = 18 := by
  have h :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq 3 N 18).2 (by
      norm_num
      exact hN)
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod27_eq_19_of_exponent
    {N : Nat} (hN : N % 27 = 19) : affineOrbit N % 27 = 19 := by
  have h :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq 3 N 19).2 (by
      norm_num
      exact hN)
  norm_num [affineOrbit] at h
  exact h

private theorem affineOrbit_mod27_eq_25_of_exponent
    {N : Nat} (hN : N % 27 = 25) : affineOrbit N % 27 = 25 := by
  have h :=
    (affineOrbit_residue_eq_iff_exponent_residue_eq 3 N 25).2 (by
      norm_num
      exact hN)
  norm_num [affineOrbit] at h
  exact h

/-- Third-trit affine kill for exponent residue 18.  The actual affine source
reads `0,0,2`; channel 1 therefore enters state 0, stays in state 0, and the
third read `2` terminates the bad state. -/
theorem commonTwo_of_mod27_eighteen
    (N : Nat) (hN : N % 27 = 18) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hAmod : A % 27 = 18 := by
    dsimp [A]
    exact affineOrbit_mod27_eq_18_of_exponent hN
  have hd0 : lowDigit A = 0 := by
    unfold lowDigit
    omega
  have hd1 : lowDigit (tail3 A) = 0 := by
    unfold lowDigit tail3
    omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by
    unfold lowDigit tail3
    omega
  have hbad1 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad0 : BadChannel 0 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad1
    simpa using hbad1
  have hbad00 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_zero_iff, hd1] at hbad0
    simpa using hbad0
  rw [badChannel_zero_iff, hd2] at hbad00
  simpa using hbad00

/-- Third-trit affine kill for exponent residue 19.  The source reads
`1,0,2`: state 1 survives the first read, enters state 0 on the second, and
is killed by the third read `2`. -/
theorem commonTwo_of_mod27_nineteen
    (N : Nat) (hN : N % 27 = 19) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hAmod : A % 27 = 19 := by
    dsimp [A]
    exact affineOrbit_mod27_eq_19_of_exponent hN
  have hd0 : lowDigit A = 1 := by
    unfold lowDigit
    omega
  have hd1 : lowDigit (tail3 A) = 0 := by
    unfold lowDigit tail3
    omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by
    unfold lowDigit tail3
    omega
  have hbad1 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad11 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad1
    simpa using hbad1
  have hbad10 : BadChannel 0 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad11
    simpa using hbad11
  rw [badChannel_zero_iff, hd2] at hbad10
  simpa using hbad10

/-- Third-trit affine kill for exponent residue 25.  The source reads
`1,2,2`: state 1 survives twice, the second read enters state 3, and state 3
cannot survive the third read `2`. -/
theorem commonTwo_of_mod27_twentyfive
    (N : Nat) (hN : N % 27 = 25) : CommonTwo N := by
  by_contra hNo
  let A := affineOrbit N
  have hAmod : A % 27 = 25 := by
    dsimp [A]
    exact affineOrbit_mod27_eq_25_of_exponent hN
  have hd0 : lowDigit A = 1 := by
    unfold lowDigit
    omega
  have hd1 : lowDigit (tail3 A) = 2 := by
    unfold lowDigit tail3
    omega
  have hd2 : lowDigit (tail3 (tail3 A)) = 2 := by
    unfold lowDigit tail3
    omega
  have hbad1 : BadChannel 1 A := by
    dsimp [A]
    exact (noCommonTwo_iff_badChannel_one N).mp hNo
  have hbad11 : BadChannel 1 (tail3 A) := by
    rw [badChannel_one_iff, hd0] at hbad1
    simpa using hbad1
  have hbad13 : BadChannel 3 (tail3 (tail3 A)) := by
    rw [badChannel_one_iff, hd1] at hbad11
    simpa using hbad11
  rw [badChannel_three_iff, hd2] at hbad13
  simpa using hbad13

/-- The three genuinely new third-trit affine kill classes produce actual
physical Happy rows directly.  No global direct-existence hypothesis and no
navigation/transport theorem is used. -/
theorem physical_happy_of_mod27_affine_third_kills
    (N : Nat)
    (hN : N % 27 = 18 ∨ N % 27 = 19 ∨ N % 27 = 25) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  rcases hN with h18 | h19 | h25
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod27_eighteen N h18)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod27_nineteen N h19)
  · exact commonTwo_to_physical_happy_row N (commonTwo_of_mod27_twentyfive N h25)

/-- Task-3.3-shaped relocation constructor for the new third-trit sector. -/
theorem four_power_happy_propagates_of_next_mod27_affine_third_kills
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 27 = 18 ∨ (K+1) % 27 = 19 ∨ (K+1) % 27 = 25) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_mod27_affine_third_kills (K+1) hNext

#check commonTwo_of_mod27_eighteen
#check commonTwo_of_mod27_nineteen
#check commonTwo_of_mod27_twentyfive
#check physical_happy_of_mod27_affine_third_kills
#check four_power_happy_propagates_of_next_mod27_affine_third_kills
#print axioms commonTwo_of_mod27_eighteen
#print axioms commonTwo_of_mod27_nineteen
#print axioms commonTwo_of_mod27_twentyfive
#print axioms physical_happy_of_mod27_affine_third_kills
#print axioms four_power_happy_propagates_of_next_mod27_affine_third_kills

end GSTFourPowerAffineThirdTrit
