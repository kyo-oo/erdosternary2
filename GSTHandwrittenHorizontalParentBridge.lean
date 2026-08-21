import GSTHandwrittenChildFirstBig1

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTInfiniteV2

/-- The canonical prefix-one horizontal multiplier is literally an even-length
binary bridge: 4^(3^s) = 2^(2*3^s). -/
theorem gpt56_parent_multiplier_is_binary_bridge
    (s : Nat) :
    4^(3^s) = 2^(2 * 3^s) := by
  calc
    4^(3^s) = (2^2)^(3^s) := by norm_num
    _ = 2^(2 * 3^s) := by rw [Nat.pow_mul]

/-- At the terminal column of that physical binary segment, the literal binary
column is exactly the canonical parent multiplier applied to T. -/
theorem gpt56_parent_binary_column_exact
    (s T : Nat) :
    2^(2 * 3^s) * T = 4^(3^s) * T := by
  rw [← gpt56_parent_multiplier_is_binary_bridge]

/-- Consequently the handwritten information digit at the end of the binary
segment is the ordinary ternary digit of the horizontally transported child. -/
theorem gpt56_parent_binary_endpoint_digit
    (s T q : Nat) :
    GSTPhysicalKernel.binaryColumnDigit T q (2 * 3^s) =
      gstDigitS (4^(3^s) * T) q := by
  unfold GSTPhysicalKernel.binaryColumnDigit gstDigitS
  rw [gpt56_parent_binary_column_exact]

/-- And the incoming x2 carry at that endpoint is the literal carry generated
by the low residue of the horizontally transported child. -/
theorem gpt56_parent_binary_endpoint_carry
    (s T q : Nat) :
    GSTPhysicalKernel.binaryColumnCarry T q (2 * 3^s) =
      (2 * ((4^(3^s) * T) % 3^q)) / 3^q := by
  unfold GSTPhysicalKernel.binaryColumnCarry
  rw [gpt56_parent_binary_column_exact]

/-- If the physical path has not hit BIG1 before the complete parent multiplier
segment, every information vertex through that endpoint is BIG2. -/
theorem gpt56_no_big1_before_parent_endpoint_forces_big2
    (s T q : Nat)
    (hd2 : gstDigit T q = 2)
    (hno : ∀ r, r ≤ 2 * 3^s →
      GSTPhysicalKernel.binaryColumnDigit T q r ≠ 1) :
    GSTPhysicalKernel.binaryColumnDigit T q (2 * 3^s) = 2 := by
  let a : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnCarry T q r
  let d : Nat → Nat := fun r => GSTPhysicalKernel.binaryColumnDigit T q r
  let K := 2 * 3^s
  have hpath : GSTInfiniteBridgePathS a d := by
    simpa [a, d] using gpt56_binary_row_path T q
  have hd0eq : d 0 = 2 := by
    dsimp [d]
    simpa [GSTPhysicalKernel.binaryColumnDigit, gstDigit] using hd2
  have hd0 : d 0 ≠ 0 := by omega
  obtain ⟨N, hfirst⟩ := gpt56_physical_path_forces_first_big1 T q (by
    simpa [d] using hd0)
  have hN : 1 ≤ N := by
    by_contra hN0
    have hNz : N = 0 := by omega
    subst N
    have hfirst0 := hfirst.1
    omega
  have hKlt : K < N := by
    by_contra hnot
    have hNle : N ≤ K := by omega
    have hneq := hno N (by simpa [K] using hNle)
    exact hneq hfirst.1
  have hbig2 := gst_before_first_big1_all_big2S
    a d hpath hd0 N hN (by simpa [d] using hfirst) K hKlt
  simpa [d, K] using hbig2

/-- Same endpoint statement in the canonical 4^(3^s)*T coordinates. -/
theorem gpt56_no_big1_before_parent_endpoint_digit_two
    (s T q : Nat)
    (hd2 : gstDigit T q = 2)
    (hno : ∀ r, r ≤ 2 * 3^s →
      GSTPhysicalKernel.binaryColumnDigit T q r ≠ 1) :
    gstDigitS (4^(3^s) * T) q = 2 := by
  rw [← gpt56_parent_binary_endpoint_digit]
  exact gpt56_no_big1_before_parent_endpoint_forces_big2 s T q hd2 hno

#check gpt56_parent_multiplier_is_binary_bridge
#check gpt56_parent_binary_endpoint_digit
#check gpt56_no_big1_before_parent_endpoint_digit_two
#print axioms gpt56_parent_multiplier_is_binary_bridge
#print axioms gpt56_no_big1_before_parent_endpoint_digit_two
