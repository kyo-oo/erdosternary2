import GSTHandwrittenPhysicalNoBig1

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- A genuine child Happy gate cannot remain in the handwritten I!=BIG1
sector forever.  Its literal physical binary-column path hits BIG1 at a finite
first column. -/
theorem gpt56_child_happy_forces_first_big1
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    ∃ N, 1 ≤ N ∧
      GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N := by
  have hd0eq : GSTPhysicalKernel.binaryColumnDigit T q 0 = 2 := by
    dsimp [GSTPhysicalKernel.binaryColumnDigit]
    simpa [_root_.GSTSeededHappyS, _root_.gstDigitS] using hgate.1
  have hd0 : GSTPhysicalKernel.binaryColumnDigit T q 0 ≠ 0 := by omega
  obtain ⟨N, hfirst⟩ := gpt56_physical_path_forces_first_big1 T q hd0
  have hN : 1 ≤ N := by
    by_contra hnot
    have hN0 : N = 0 := by omega
    subst N
    omega
  exact ⟨N, hN, hfirst⟩

/-- The first physical BIG1 is preceded by the exact handwritten DESTROY
boundary: incoming bit 0, information BIG2, mass 4, event 5. -/
theorem gpt56_child_happy_forces_destroy_boundary
    (T q : Nat)
    (hgate : GSTSeededHappyS 0 T q) :
    ∃ N, 1 ≤ N ∧
      GSTFirstBig1AtS
        (fun r => GSTPhysicalKernel.binaryColumnDigit T q r) N ∧
      let j := N - 1
      GSTPhysicalKernel.binaryColumnCarry T q j = 0 ∧
      GSTPhysicalKernel.binaryColumnDigit T q j = 2 ∧
      gstBinaryBridgeMassS
        (GSTPhysicalKernel.binaryColumnCarry T q j)
        (GSTPhysicalKernel.binaryColumnDigit T q j) = 4 ∧
      gstBinaryBridgeEventS
        (GSTPhysicalKernel.binaryColumnCarry T q j)
        (GSTPhysicalKernel.binaryColumnDigit T q j) = 5 := by
  obtain ⟨N, hN, hfirst⟩ := gpt56_child_happy_forces_first_big1 T q hgate
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hd0eq : d 0 = 2 := by
    dsimp [d, GSTPhysicalKernel.binaryColumnDigit]
    simpa [_root_.GSTSeededHappyS, _root_.gstDigitS] using hgate.1
  have hd0 : d 0 ≠ 0 := by omega
  have hboundary := gst_first_big1_boundary_is_destroyS
    a d hpath hd0 N hN (by simpa [d] using hfirst)
  refine ⟨N, hN, hfirst, ?_⟩
  simpa [a, d] using hboundary

#check gpt56_child_happy_forces_first_big1
#check gpt56_child_happy_forces_destroy_boundary
#print axioms gpt56_child_happy_forces_first_big1
#print axioms gpt56_child_happy_forces_destroy_boundary
