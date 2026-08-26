import GSTNavigationCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-- Exact public creation certificate required by the production seam. -/
def GSTFourPowerCreationCertificate (k p : Nat) : Prop :=
  1 ≤ p ∧
  (4^k) / 3^p % 3 = 2 ∧
    ((4 * ((4^k) % 3^p)) / 3^p % 3 = 0 ∨
      ((4 * ((4^k) % 3^p)) / 3^p % 3 = 1 ∧
        (4^k) / 3^(p+1) % 3 = 2))

/-- Removing the forced `s+1` ternary prefix shifts every tail digit exactly. -/
theorem gst_navigation_tail_digit_shiftS
    (s b j : Nat) (hs : 1 ≤ s) :
    gstDigit (4^(3^s * b)) (s+1+j) =
      gstDigit (gstNavigationConstant s b) j := by
  unfold gstDigit
  have hDpos : 0 < 3^(s+1) := Nat.pow_pos (by decide)
  have hD9 : 9 ≤ 3^(s+1) := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h1lt : 1 < 3^(s+1) := by omega
  have hdecomp := gst_navigation_core_decompositionS s b hs
  have hdiv :
      4^(3^s * b) / 3^(s+1) = gstNavigationConstant s b := by
    rw [hdecomp, Nat.add_mul_div_left _ _ hDpos,
      Nat.div_eq_of_lt h1lt, Nat.zero_add]
  rw [show s + 1 + j = (s+1)+j by omega, Nat.pow_add,
    ← Nat.div_div_eq_div_mul, hdiv]

/-- The same prefix removal preserves the physical x4 carry exactly. -/
theorem gst_navigation_tail_carry_shiftS
    (s b j : Nat) (hs : 1 ≤ s) :
    gstCarry (4^(3^s * b)) (s+1+j) =
      gstCarry (gstNavigationConstant s b) j := by
  let D := 3^(s+1)
  let J := 3^j
  let Q := gstNavigationConstant s b
  have hDpos : 0 < D := by
    dsimp [D]
    exact Nat.pow_pos (by decide)
  have hJpos : 0 < J := by
    dsimp [J]
    exact Nat.pow_pos (by decide)
  have hD9 : 9 ≤ D := by
    dsimp [D]
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4ltD : 4 < D := by omega
  have hQsplit : Q = Q % J + J * (Q / J) := by
    simpa [Nat.mul_comm] using (Nat.mod_add_div Q J).symm
  have hdecomp : 4^(3^s * b) = 1 + D * Q := by
    simpa [D, Q] using gst_navigation_core_decompositionS s b hs
  have hshape :
      4^(3^s * b) =
        (1 + D * (Q % J)) + (D * J) * (Q / J) := by
    calc
      4^(3^s * b) = 1 + D * Q := hdecomp
      _ = (1 + D * (Q % J)) + (D * J) * (Q / J) := by
        conv_lhs => rw [hQsplit]
        ring
  have hRlt : Q % J < J := Nat.mod_lt _ hJpos
  have hlow : 1 + D * (Q % J) < D * J := by
    calc
      1 + D * (Q % J) < D + D * (Q % J) := by omega
      _ = D * ((Q % J) + 1) := by ring
      _ ≤ D * J := Nat.mul_le_mul_left D (Nat.succ_le_of_lt hRlt)
  have hmod :
      4^(3^s * b) % (D * J) = 1 + D * (Q % J) := by
    rw [hshape]
    simp [Nat.mod_eq_of_lt hlow]
  unfold gstCarry
  have hpow : 3^(s+1+j) = D * J := by
    dsimp [D, J]
    rw [show s+1+j = (s+1)+j by omega, Nat.pow_add]
  rw [hpow, hmod]
  rw [← Nat.div_div_eq_div_mul]
  have hnum : 4 * (1 + D * (Q % J)) = 4 + D * (4 * (Q % J)) := by ring
  rw [hnum, Nat.add_mul_div_left _ _ hDpos,
    Nat.div_eq_of_lt h4ltD, Nat.zero_add]

/-- Decode the Navigation space tag back into the two physical Happy carries. -/
theorem gst_navigation_witness_physicalS
    (R : Nat) (h : GSTNavigationWitness R) :
    ∃ j, gstDigit R j = 2 ∧ (gstCarry R j = 0 ∨ gstCarry R j = 3) := by
  obtain ⟨j, hd, hspace⟩ := h
  refine ⟨j, hd, ?_⟩
  rcases hspace with hplus | hnull
  · right
    by_cases h0 : gstCarry R j = 0
    · simp [gstSpaceAt, h0] at hplus
    · by_cases h3 : gstCarry R j = 3
      · exact h3
      · simp [gstSpaceAt, h0, h3] at hplus
  · left
    by_cases h0 : gstCarry R j = 0
    · exact h0
    · by_cases h3 : gstCarry R j = 3
      · simp [gstSpaceAt, h0, h3] at hnull
      · simp [gstSpaceAt, h0, h3] at hnull

/-- A Happy gate in the Navigation tail gives the exact production creation
certificate in the original perfect power. -/
theorem gst_four_power_creation_of_navigation_witnessS
    (s b : Nat) (hs : 1 ≤ s)
    (hnav : GSTNavigationWitness (gstNavigationConstant s b)) :
    ∃ p, GSTFourPowerCreationCertificate (3^s * b) p := by
  obtain ⟨j, hd, hC⟩ := gst_navigation_witness_physicalS _ hnav
  let p := s + 1 + j
  have hdShift := gst_navigation_tail_digit_shiftS s b j hs
  have hCShift := gst_navigation_tail_carry_shiftS s b j hs
  refine ⟨p, ?_⟩
  unfold GSTFourPowerCreationCertificate
  constructor
  · dsimp [p]
    omega
  constructor
  · change gstDigit (4^(3^s * b)) p = 2
    dsimp [p]
    rw [hdShift]
    exact hd
  · left
    change gstCarry (4^(3^s * b)) p % 3 = 0
    dsimp [p]
    rw [hCShift]
    rcases hC with h0 | h3
    · simp [h0]
    · simp [h3]

/-- First major universal branch: if the reduced exponent begins with ternary
trit two, the Navigation tail is already Happy at position zero. -/
theorem gst_four_power_creation_scaled_unit_twoS
    (s b : Nat) (hs : 1 ≤ s) (hb2 : b % 3 = 2) :
    ∃ p, GSTFourPowerCreationCertificate (3^s * b) p := by
  have hmod := gst_navigation_core_mod3_allS s b hs
  have hd : gstDigit (gstNavigationConstant s b) 0 = 2 := by
    simpa [gstDigit] using hmod.trans hb2
  have hC : gstCarry (gstNavigationConstant s b) 0 = 0 := by
    simp [gstCarry, Nat.mod_one]
  have hnav : GSTNavigationWitness (gstNavigationConstant s b) :=
    gst_navigation_core_witness_of_digit_carry_zeroS _ 0 hd hC
  exact gst_four_power_creation_of_navigation_witnessS s b hs hnav

/-- Small production bases, proved by literal arithmetic only. -/
theorem gst_four_power_creation_base5S :
    ∃ p, GSTFourPowerCreationCertificate 5 p := by
  refine ⟨2, ?_⟩
  norm_num [GSTFourPowerCreationCertificate]

theorem gst_four_power_creation_base6S :
    ∃ p, GSTFourPowerCreationCertificate 6 p := by
  refine ⟨2, ?_⟩
  norm_num [GSTFourPowerCreationCertificate]

theorem gst_four_power_creation_base8S :
    ∃ p, GSTFourPowerCreationCertificate 8 p := by
  refine ⟨4, ?_⟩
  norm_num [GSTFourPowerCreationCertificate]

theorem gst_four_power_creation_base9S :
    ∃ p, GSTFourPowerCreationCertificate 9 p := by
  refine ⟨7, ?_⟩
  norm_num [GSTFourPowerCreationCertificate]

theorem gst_four_power_creation_base10S :
    ∃ p, GSTFourPowerCreationCertificate 10 p := by
  refine ⟨10, ?_⟩
  norm_num [GSTFourPowerCreationCertificate]

#check gst_navigation_tail_digit_shiftS
#check gst_navigation_tail_carry_shiftS
#check gst_four_power_creation_of_navigation_witnessS
#check gst_four_power_creation_scaled_unit_twoS
#print axioms gst_navigation_tail_digit_shiftS
#print axioms gst_navigation_tail_carry_shiftS
#print axioms gst_four_power_creation_of_navigation_witnessS
#print axioms gst_four_power_creation_scaled_unit_twoS
#print axioms gst_four_power_creation_base5S
#print axioms gst_four_power_creation_base6S
#print axioms gst_four_power_creation_base8S
#print axioms gst_four_power_creation_base9S
#print axioms gst_four_power_creation_base10S