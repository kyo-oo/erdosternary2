import GSTFourPowerDirectExistenceInline
import GSTFourPowerAffineRenormalizedOrbit

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace GSTFourPowerUniversalInduction

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge
open GSTFourPowerAffineRenormalizedOrbit

/-- The exact remaining branch descent package for the minimal-counterexample
proof.  These three implications say that any bad branch after consuming one
ternary exponent digit descends to the parent affine bad state. -/
def BranchBadDescent : Prop :=
  (∀ q : Nat,
    BadChannel 0 (renormOrbit q) →
      BadChannel 1 (affineOrbit q)) ∧
  (∀ q : Nat,
    BadChannel 1 (4 * renormOrbit q) →
      BadChannel 1 (affineOrbit q)) ∧
  (∀ q : Nat,
    BadChannel 3 (16 * renormOrbit q + 1) →
      BadChannel 1 (affineOrbit q))

private theorem commonTwo_8 : CommonTwo 8 := by
  refine ⟨4, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_9 : CommonTwo 9 := by
  refine ⟨7, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_10 : CommonTwo 10 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_11 : CommonTwo 11 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_12 : CommonTwo 12 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_13 : CommonTwo 13 := by
  refine ⟨14, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_14 : CommonTwo 14 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_21 : CommonTwo 21 := by
  refine ⟨5, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_22 : CommonTwo 22 := by
  refine ⟨6, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem commonTwo_23 : CommonTwo 23 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;>
    norm_num [GSTFourPowerDirectResidue.digit3]

private theorem no_bad_channel_one_of_commonTwo
    (K : Nat) (hCommon : CommonTwo K) :
    ¬ BadChannel 1 (affineOrbit K) := by
  intro hBad
  exact ((noCommonTwo_iff_badChannel_one K).2 hBad) hCommon

private theorem no_bad_channel_one_finite_base
    (K : Nat) (hK5 : 5 ≤ K) (hK15 : K < 15) (hK7 : K ≠ 7) :
    ¬ BadChannel 1 (affineOrbit K) := by
  interval_cases K
  · exact no_bad_channel_one_of_commonTwo 5
      (commonTwo_of_mod9_five_or_six 5 (by decide))
  · exact no_bad_channel_one_of_commonTwo 6
      (commonTwo_of_mod9_five_or_six 6 (by decide))
  · exact (hK7 rfl).elim
  · exact no_bad_channel_one_of_commonTwo 8 commonTwo_8
  · exact no_bad_channel_one_of_commonTwo 9 commonTwo_9
  · exact no_bad_channel_one_of_commonTwo 10 commonTwo_10
  · exact no_bad_channel_one_of_commonTwo 11 commonTwo_11
  · exact no_bad_channel_one_of_commonTwo 12 commonTwo_12
  · exact no_bad_channel_one_of_commonTwo 13 commonTwo_13
  · exact no_bad_channel_one_of_commonTwo 14 commonTwo_14

private theorem no_bad_channel_one_q_eq_seven_children
    (K q r : Nat) (hq : q = K / 3) (hr : r = K % 3)
    (hsplit : K = 3*q + r) (hrlt : r < 3) (hq7 : q = 7) :
    ¬ BadChannel 1 (affineOrbit K) := by
  subst q
  interval_cases r
  · have hK : K = 21 := by omega
    subst K
    exact no_bad_channel_one_of_commonTwo 21 commonTwo_21
  · have hK : K = 22 := by omega
    subst K
    exact no_bad_channel_one_of_commonTwo 22 commonTwo_22
  · have hK : K = 23 := by omega
    subst K
    exact no_bad_channel_one_of_commonTwo 23 commonTwo_23

/-- Minimal-counterexample induction: the three renormalized branch descents
are enough to kill bad affine channel `B₁` for every admissible exponent. -/
theorem no_bad_affine_channel_one_of_branch_bad_descent
    (hDesc : BranchBadDescent) :
    ∀ K : Nat, 5 ≤ K → K ≠ 7 →
      ¬ BadChannel 1 (affineOrbit K) := by
  intro K
  induction K using Nat.strong_induction_on with
  | h K ih =>
      intro hK5 hK7 hBad
      by_cases hK15 : K < 15
      · exact no_bad_channel_one_finite_base K hK5 hK15 hK7 hBad
      · let q : Nat := K / 3
        let r : Nat := K % 3
        have hrlt : r < 3 := by
          dsimp [r]
          exact Nat.mod_lt K (by decide)
        have hsplit : K = 3*q + r := by
          dsimp [q, r]
          omega
        have hqLt : q < K := by
          dsimp [q]
          omega
        have hq5 : 5 ≤ q := by
          dsimp [q]
          omega
        by_cases hq7 : q = 7
        · exact no_bad_channel_one_q_eq_seven_children K q r rfl rfl hsplit hrlt hq7 hBad
        · have hParentNoBad : ¬ BadChannel 1 (affineOrbit q) :=
            ih q hqLt hq5 hq7
          have hNoK : ¬ CommonTwo K :=
            (noCommonTwo_iff_badChannel_one K).2 hBad
          interval_cases r
          · have hKshape : K = 3*q := by omega
            have hNo3 : ¬ CommonTwo (3*q) := by
              simpa [hKshape] using hNoK
            have hBranch : BadChannel 0 (renormOrbit q) :=
              (noCommonTwo_three_mul_renorm_iff q).1 hNo3
            exact hParentNoBad (hDesc.1 q hBranch)
          · have hKshape : K = 3*q + 1 := by omega
            have hNo3 : ¬ CommonTwo (3*q + 1) := by
              simpa [hKshape] using hNoK
            have hBranch : BadChannel 1 (4 * renormOrbit q) :=
              (noCommonTwo_three_mul_add_one_renorm_iff q).1 hNo3
            exact hParentNoBad (hDesc.2.1 q hBranch)
          · have hKshape : K = 3*q + 2 := by omega
            have hNo3 : ¬ CommonTwo (3*q + 2) := by
              simpa [hKshape] using hNoK
            have hBranch : BadChannel 3 (16 * renormOrbit q + 1) :=
              (noCommonTwo_three_mul_add_two_renorm_iff q).1 hNo3
            exact hParentNoBad (hDesc.2.2 q hBranch)

/-- Universal direct existence from the branch descent package. -/
theorem fourPowerDirectExistence_of_branch_bad_descent
    (hDesc : BranchBadDescent) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  by_contra hNo
  exact
    (no_bad_affine_channel_one_of_branch_bad_descent hDesc K hK5 hK7)
      ((noCommonTwo_iff_badChannel_one K).1 hNo)

#check BranchBadDescent
#check no_bad_affine_channel_one_of_branch_bad_descent
#check fourPowerDirectExistence_of_branch_bad_descent
#print axioms no_bad_affine_channel_one_of_branch_bad_descent
#print axioms fourPowerDirectExistence_of_branch_bad_descent

end GSTFourPowerUniversalInduction
