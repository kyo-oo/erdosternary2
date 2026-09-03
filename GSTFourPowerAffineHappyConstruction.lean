import GSTFourPowerAffinePeelClassifier
import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffineHappyConstruction

open GSTFourPowerAffinePeelClassifier
open GSTFourPowerDirectHappyBridge

/-- Direct physical construction on affine exponent branch `0`.  The affine
classifier kills a bad state when the next exponent trit is `2`; the resulting
`CommonTwo` witness is converted at the very same row into an actual physical
Happy cell. -/
theorem physical_happy_three_mul_of_q_mod_three_eq_two
    (u : Nat) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u)) q) := by
  exact commonTwo_to_physical_happy_row
    (3*u)
    (commonTwo_three_mul_of_q_mod_three_eq_two u hu)

/-- Direct physical construction on affine exponent branch `2`.  When the next
exponent trit is `1`, the twisted second affine read is `2`, terminating state
`3`; again the common-two row itself is the physical Happy row. -/
theorem physical_happy_three_mul_add_two_of_q_mod_three_eq_one
    (u : Nat) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(3*u+2)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(3*u+2)) q) := by
  exact commonTwo_to_physical_happy_row
    (3*u+2)
    (commonTwo_three_mul_add_two_of_q_mod_three_eq_one u hu)

/-- Relocation-shaped branch `0` constructor.  No global direct-existence
assumption is used: if the next exponent itself has affine suffix `20`, a real
Happy row on `4^(K+1)` is constructed directly. -/
theorem relocated_physical_happy_of_next_three_mul
    (K u : Nat) (hEq : K + 1 = 3*u) (hu : u % 3 = 2) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hEq]
  exact physical_happy_three_mul_of_q_mod_three_eq_two u hu

/-- Relocation-shaped branch `2` constructor.  If the next exponent has affine
suffix `12` (least-significant trit first), the direct finite-state kill law
constructs an actual relocated Happy row `q ≥ 1` with no navigation route and
no `FourPowerDirectExistence` hypothesis. -/
theorem relocated_physical_happy_of_next_three_mul_add_two
    (K u : Nat) (hEq : K + 1 = 3*u+2) (hu : u % 3 = 1) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  rw [hEq]
  exact physical_happy_three_mul_add_two_of_q_mod_three_eq_one u hu

/-- The two certified affine kill branches combine into the exact mod-9
physical constructor.  This is still derived only from the affine bad-state
machine: residues `6` and `5` are reconstructed as `3*(3t+2)` and
`3*(3t+1)+2`, respectively, and the corresponding physical constructor is
applied.  No global direct-existence hypothesis occurs. -/
theorem physical_happy_of_exponent_mod_nine_five_or_six
    (N : Nat) (hN : N % 9 = 5 ∨ N % 9 = 6) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^N) q)
        (GSTCanonicalTailStateIso.digit3 (4^N) q) := by
  have hdecomp : N = N % 9 + 9 * (N / 9) :=
    (Nat.mod_add_div N 9).symm
  rcases hN with h5 | h6
  · let u : Nat := 3 * (N / 9) + 1
    have hEq : N = 3*u + 2 := by
      dsimp [u]
      rw [h5] at hdecomp
      omega
    have hu : u % 3 = 1 := by
      simp [u, Nat.add_mod, Nat.mul_mod]
    rw [hEq]
    exact physical_happy_three_mul_add_two_of_q_mod_three_eq_one u hu
  · let u : Nat := 3 * (N / 9) + 2
    have hEq : N = 3*u := by
      dsimp [u]
      rw [h6] at hdecomp
      omega
    have hu : u % 3 = 2 := by
      simp [u, Nat.add_mod, Nat.mul_mod]
    rw [hEq]
    exact physical_happy_three_mul_of_q_mod_three_eq_two u hu

/-- Task-3.3-shaped direct relocation on the complete affine two-trit kill
sector.  The source Happy witness is intentionally not transported: once the
next exponent lies in residue `5` or `6` mod `9`, the affine classifier builds
a new physical Happy row directly on the next sheet. -/
theorem four_power_happy_propagates_of_next_mod_nine
    (K p : Nat) (hK : 8 ≤ K) (hp : 1 ≤ p)
    (hHappy :
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^K) p)
        (GSTCanonicalTailStateIso.digit3 (4^K) p))
    (hNext : (K+1) % 9 = 5 ∨ (K+1) % 9 = 6) :
    ∃ q : Nat, 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  exact physical_happy_of_exponent_mod_nine_five_or_six (K+1) hNext

#check physical_happy_three_mul_of_q_mod_three_eq_two
#check physical_happy_three_mul_add_two_of_q_mod_three_eq_one
#check relocated_physical_happy_of_next_three_mul
#check relocated_physical_happy_of_next_three_mul_add_two
#check physical_happy_of_exponent_mod_nine_five_or_six
#check four_power_happy_propagates_of_next_mod_nine
#print axioms physical_happy_three_mul_of_q_mod_three_eq_two
#print axioms physical_happy_three_mul_add_two_of_q_mod_three_eq_one
#print axioms relocated_physical_happy_of_next_three_mul
#print axioms relocated_physical_happy_of_next_three_mul_add_two
#print axioms physical_happy_of_exponent_mod_nine_five_or_six
#print axioms four_power_happy_propagates_of_next_mod_nine

end GSTFourPowerAffineHappyConstruction
