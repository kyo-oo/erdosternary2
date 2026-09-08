import GSTCanonicalTailStateIso
import GSTGraphV2PerfectPowerAncestry
import GSTFourPowerOntologicalAdapter

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerThreeStepBadnessDescent

/-- Complete absence of physical Happy cells from ternary row three upward. -/
def BadAboveThree (K : Nat) : Prop :=
  ∀ p : Nat, 3 ≤ p →
    ¬ GSTU2DEventTransport.HappyCell
      (GSTCanonicalSevenAxisBridge.carry4 (4^K) p)
      (GSTCanonicalSevenAxisBridge.digit3 (4^K) p)

/-- The genuinely all-depth replacement for the former one-row collision seam.

Its contrapositive is stronger than the old theorem: every Happy cell above
row three on exponent K forces some Happy cell above row three on exponent
K+3, with no inherited witness row and no bounded observation horizon. -/
def ThreeStepBadnessDescent : Prop :=
  ∀ K : Nat, BadAboveThree (K+3) → BadAboveThree K

/-- Graph formulation of BadAboveThree on the width-three right boundary. -/
theorem badAboveThree_iff_graph_right_bad (K : Nat) :
    BadAboveThree (K+3) ↔
      ∀ j : Nat, ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.digit := by
  constructor
  · intro h j hHappy
    apply h (3+j) (by omega)
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex,
      Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hHappy
  · intro h p hp hHappy
    let j := p - 3
    have hpj : 3 + j = p := by
      dsimp [j]
      omega
    apply h j
    have hpow : 4^3 * 4^K = 4^(K+3) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [← hpow] at hHappy
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex, hpj,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hHappy

/-- Graph formulation of BadAboveThree on the left boundary. -/
theorem badAboveThree_iff_graph_left_bad (K : Nat) :
    BadAboveThree K ↔
      ∀ j : Nat, ¬ GSTU2DEventTransport.HappyCell
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+j)).seven.carry
        (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+j)).seven.digit := by
  constructor
  · intro h j hHappy
    apply h (3+j) (by omega)
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex] using hHappy
  · intro h p hp hHappy
    let j := p - 3
    have hpj : 3 + j = p := by
      dsimp [j]
      omega
    apply h j
    simpa [GSTGraphV2InfiniteControl.graph,
      GSTGraphV2InfiniteControl.cell,
      GSTCanonicalSevenAxisBridge.vertex, hpj] using hHappy

/-- Once ThreeStepBadnessDescent is established, the old collision is immediate.
This theorem is kernel-clean and deliberately contains no arithmetic closer. -/
theorem collision_of_three_step_badness_descent
    (hDescent : ThreeStepBadnessDescent)
    (K q : Nat)
    (hChild : GSTU2DEventTransport.HappyCell
      (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.carry
      (GSTGraphV2InfiniteControl.graph (4^K) 0 (3+q)).seven.digit)
    (hRightBad : ∀ j, ¬ GSTU2DEventTransport.HappyCell
      (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.carry
      (GSTGraphV2InfiniteControl.graph (4^K) 3 (3+j)).seven.digit) :
    False := by
  have hBadNext : BadAboveThree (K+3) :=
    (badAboveThree_iff_graph_right_bad K).2 hRightBad
  have hBadHere : BadAboveThree K := hDescent K hBadNext
  have hLeftBad :=
    (badAboveThree_iff_graph_left_bad K).1 hBadHere q
  exact hLeftBad hChild

/-- Strong induction no longer needs a row-transport theorem: the whole bad
boundary descends by three exponents. -/
theorem happy_ge_three_of_three_step_badness_descent
    (hDescent : ThreeStepBadnessDescent) :
    ∀ k : Nat, 8 ≤ k →
      ∃ p : Nat, 3 ≤ p ∧
        GSTU2DEventTransport.HappyCell
          (GSTCanonicalSevenAxisBridge.carry4 (4^k) p)
          (GSTCanonicalSevenAxisBridge.digit3 (4^k) p) := by
  intro k hk
  induction k using Nat.strongRecOn with
  | ind k ih =>
      by_cases hk11 : 11 ≤ k
      · have hk3 : 8 ≤ k - 3 := by omega
        obtain ⟨p, hp3, hpHappy⟩ := ih (k-3) (by omega) hk3
        by_contra hNo
        have hBadK : BadAboveThree k := by
          intro r hr hHappy
          apply hNo
          exact ⟨r, hr, hHappy⟩
        have hBadPrev : BadAboveThree (k-3) := by
          have hshape : (k-3)+3 = k := by omega
          rw [← hshape] at hBadK
          exact hDescent (k-3) hBadK
        exact (hBadPrev p hp3) hpHappy
      · have hkCases : k = 8 ∨ k = 9 ∨ k = 10 := by omega
        rcases hkCases with rfl | rfl | rfl
        · refine ⟨4, by decide, ?_⟩
          norm_num [GSTU2DEventTransport.HappyCell,
            GSTCanonicalSevenAxisBridge.carry4,
            GSTCanonicalSevenAxisBridge.digit3]
        · refine ⟨7, by decide, ?_⟩
          norm_num [GSTU2DEventTransport.HappyCell,
            GSTCanonicalSevenAxisBridge.carry4,
            GSTCanonicalSevenAxisBridge.digit3]
        · refine ⟨10, by decide, ?_⟩
          norm_num [GSTU2DEventTransport.HappyCell,
            GSTCanonicalSevenAxisBridge.carry4,
            GSTCanonicalSevenAxisBridge.digit3]

#check BadAboveThree
#check ThreeStepBadnessDescent
#check badAboveThree_iff_graph_right_bad
#check badAboveThree_iff_graph_left_bad
#check collision_of_three_step_badness_descent
#check happy_ge_three_of_three_step_badness_descent
#print axioms badAboveThree_iff_graph_right_bad
#print axioms collision_of_three_step_badness_descent
#print axioms happy_ge_three_of_three_step_badness_descent

end GSTFourPowerThreeStepBadnessDescent
