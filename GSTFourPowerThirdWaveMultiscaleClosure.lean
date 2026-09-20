import GSTFourPowerThirdWaveMultiscaleBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

namespace GSTFourPowerThirdWaveMultiscaleClosure

open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue
open GSTFourPowerThirdWaveMultiscaleBridge

private theorem commonTwo_5 : CommonTwo 5 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_6 : CommonTwo 6 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_8 : CommonTwo 8 := by
  refine ⟨4, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_9 : CommonTwo 9 := by
  refine ⟨7, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_10 : CommonTwo 10 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_11 : CommonTwo 11 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_12 : CommonTwo 12 := by
  refine ⟨10, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_13 : CommonTwo 13 := by
  refine ⟨14, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_14 : CommonTwo 14 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_21 : CommonTwo 21 := by
  refine ⟨5, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_22 : CommonTwo 22 := by
  refine ⟨6, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_23 : CommonTwo 23 := by
  refine ⟨2, by norm_num, ?_, ?_⟩ <;> norm_num [digit3]

private theorem commonTwo_small
    (K : Nat) (hK5 : 5 ≤ K) (hK15 : K < 15) (hK7 : K ≠ 7) :
    CommonTwo K := by
  interval_cases K
  · exact commonTwo_5
  · exact commonTwo_6
  · exact (hK7 rfl).elim
  · exact commonTwo_8
  · exact commonTwo_9
  · exact commonTwo_10
  · exact commonTwo_11
  · exact commonTwo_12
  · exact commonTwo_13
  · exact commonTwo_14

/-- The multiscale third-wave descent is sufficient for the complete direct
four-power existence law.  A hypothetical counterexample descends to its
ternary parent.  Strong induction then leaves only the finite prefix cases,
which are discharged above by exact arithmetic witnesses. -/
theorem fourPowerDirectExistence_of_thirdWaveNoCommonDescent
    (hDesc : ThirdWaveNoCommonDescent) :
    FourPowerDirectExistence := by
  intro K hK5 hK7
  induction K using Nat.strongRecOn with
  | ind K ih =>
      by_contra hNo
      let q := K / 3
      let r := K % 3
      have hrlt : r < 3 := by
        dsimp [r]
        exact Nat.mod_lt _ (by decide)
      have hKqr : K = 3 * q + r := by
        dsimp [q, r]
        omega
      have hNoq : ¬ CommonTwo q := by
        have hrCases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
        rcases hrCases with rfl | rfl | rfl
        · apply hDesc.1 q
          simpa [hKqr] using hNo
        · apply hDesc.2.1 q
          simpa [hKqr] using hNo
        · apply hDesc.2.2 q
          simpa [hKqr] using hNo
      have hqLt : q < K := by
        dsimp [q]
        exact Nat.div_lt_self (by omega) (by decide : 1 < 3)
      by_cases hq5 : 5 ≤ q
      · by_cases hq7 : q = 7
        · have hKcases : K = 21 ∨ K = 22 ∨ K = 23 := by omega
          rcases hKcases with rfl | rfl | rfl
          · exact hNo commonTwo_21
          · exact hNo commonTwo_22
          · exact hNo commonTwo_23
        · exact hNoq (ih q hqLt hq5 hq7)
      · have hK15 : K < 15 := by omega
        exact hNo (commonTwo_small K hK5 hK15 hK7)

#print axioms fourPowerDirectExistence_of_thirdWaveNoCommonDescent

end GSTFourPowerThirdWaveMultiscaleClosure
