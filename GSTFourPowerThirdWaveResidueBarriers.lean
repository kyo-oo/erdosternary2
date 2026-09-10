import GSTFourPowerThirdWaveBranchReactor

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-!
# Third-wave residue barriers

These lemmas turn a surviving third-wave branch into explicit forbidden
parent congruence classes.  They are the finite residue cuts that the universal
third-wave proof needs before the positive common-lift construction is closed.
-/

namespace GSTFourPowerThirdWaveResidueBarriers

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineRenormalizedOrbit
open GSTFourPowerThirdWaveBranchReactor

/-- Branch zero survival forbids `q ≡ 6 mod 9`, because then `3q ≡ 18 mod 27`
and row three would already create a common-two witness. -/
theorem branch_zero_forces_q_mod9_ne_six
    (q : Nat) (hBad : BadChannel 0 (renormOrbit q)) :
    q % 9 ≠ 6 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q) :=
    (noCommonTwo_three_mul_renorm_iff q).2 hBad
  rcases noCommonTwo_excludes_mod27_row_three (3*q) hNo with
    ⟨_, h18, _, _⟩
  have hmod : (3*q) % 27 = 18 := by omega
  exact h18 hmod

/-- Middle-branch survival forbids `q ≡ 6 mod 9`, because then
`3q+1 ≡ 19 mod 27`. -/
theorem branch_one_forces_q_mod9_ne_six
    (q : Nat) (hBad : BadChannel 1 (4 * renormOrbit q)) :
    q % 9 ≠ 6 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q + 1) :=
    (noCommonTwo_three_mul_add_one_renorm_iff q).2 hBad
  rcases noCommonTwo_excludes_mod27_row_three (3*q + 1) hNo with
    ⟨_, _, h19, _⟩
  have hmod : (3*q + 1) % 27 = 19 := by omega
  exact h19 hmod

/-- Middle-branch survival forbids `q ≡ 8 mod 9`, because then
`3q+1 ≡ 25 mod 27`. -/
theorem branch_one_forces_q_mod9_ne_eight
    (q : Nat) (hBad : BadChannel 1 (4 * renormOrbit q)) :
    q % 9 ≠ 8 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q + 1) :=
    (noCommonTwo_three_mul_add_one_renorm_iff q).2 hBad
  rcases noCommonTwo_excludes_mod27_row_three (3*q + 1) hNo with
    ⟨_, _, _, h25⟩
  have hmod : (3*q + 1) % 27 = 25 := by omega
  exact h25 hmod

/-- Final-branch survival forbids `q ≡ 4 mod 9`, because then
`3q+2 ≡ 14 mod 27`. -/
theorem branch_two_forces_q_mod9_ne_four
    (q : Nat) (hBad : BadChannel 3 (16 * renormOrbit q + 1)) :
    q % 9 ≠ 4 := by
  intro hq
  have hNo : ¬ CommonTwo (3*q + 2) :=
    (noCommonTwo_three_mul_add_two_renorm_iff q).2 hBad
  rcases noCommonTwo_excludes_mod27_row_three (3*q + 2) hNo with
    ⟨h14, _, _, _⟩
  have hmod : (3*q + 2) % 27 = 14 := by omega
  exact h14 hmod

#check branch_zero_forces_q_mod9_ne_six
#check branch_one_forces_q_mod9_ne_six
#check branch_one_forces_q_mod9_ne_eight
#check branch_two_forces_q_mod9_ne_four
#print axioms branch_zero_forces_q_mod9_ne_six
#print axioms branch_one_forces_q_mod9_ne_six
#print axioms branch_one_forces_q_mod9_ne_eight
#print axioms branch_two_forces_q_mod9_ne_four

end GSTFourPowerThirdWaveResidueBarriers
