import GSTFourPowerDirectTwoHundredTwentySeventhRow

def threePow237 : Nat :=
  119601704370316815093156475426420811655643446371374142778498243399164563914572619949897873671922747759658511969363

def residue237N : Nat := 238
def residue237Np1 : Nat := 239

theorem threePow237_eq : 3 ^ 237 = threePow237 := by
  native_decide

theorem digit3_row237_res238 :
    digit3 (4 ^ residue237N) 237 = 2 := by
  native_decide

theorem digit3_row237_res239 :
    digit3 (4 ^ residue237Np1) 237 = 2 := by
  native_decide

theorem commonTwo_of_pair_mod_threePow237
    (N : Nat) (hmod : N % threePow237 = residue237N) :
    CommonTwo N := by
  have hmodN : N % (3 ^ 237) = 238 := by
    simpa [threePow237_eq] using hmod
  have hmodN1 : (N + 1) % (3 ^ 237) = 239 := by
    omega
  have hN : digit3 (4 ^ N) 237 = 2 := by
    rw [digit3_pow4_period N 237]
    simpa [hmodN] using digit3_row237_res238
  have hN1 : digit3 (4 ^ (N + 1)) 237 = 2 := by
    rw [digit3_pow4_period (N + 1) 237]
    simpa [hmodN1] using digit3_row237_res239
  exact ⟨237, by omega, hN, hN1⟩

theorem row237_strict_exceed_of_pair_mod_threePow237
    (N k : Nat)
    (hmod : N % threePow237 = residue237N)
    (hk : digit3 (4 ^ N) k = 2) :
    ∃ q ≥ 1, q > k ∧
      digit3 (4 ^ N) q = 2 ∧
      digit3 (4 ^ (N + 1)) q = 2 :=
  commonTwo_twoOccurrence_digit_forces_strict_greater
    N
    (commonTwo_of_pair_mod_threePow237 N hmod)
    k
    hk

theorem row237_relocated_physical_happy_of_pair_mod_threePow237
    (N k : Nat)
    (hmod : N % threePow237 = residue237N)
    (hk : digit3 (4 ^ N) k = 2) :
    ∃ q ≥ 1,
      HappyCell
        (carry4 (4 ^ N) q)
        (digit3 (4 ^ N) q) := by
  exact commonTwo_to_physical_happy_row
    N
    (commonTwo_of_pair_mod_threePow237 N hmod)
