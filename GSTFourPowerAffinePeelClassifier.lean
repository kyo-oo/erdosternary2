import GSTFourPowerAffineClassifierBridge
import GSTFourPowerAffineExponentPeel

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerAffinePeelClassifier

open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTFourPowerAffineBadState
open GSTFourPowerAffineChannelAutomaton
open GSTFourPowerAffineClassifierBridge

/-- After exponent trit `0`, the affine coordinate tail is exactly `peel0`. -/
theorem tail3_affineOrbit_three_mul (q : Nat) :
    tail3 (affineOrbit (3*q)) = peel0 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul]
  omega

/-- After exponent trit `1`, the affine coordinate tail is exactly `peel1`. -/
theorem tail3_affineOrbit_three_mul_add_one (q : Nat) :
    tail3 (affineOrbit (3*q+1)) = peel1 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul_add_one]
  omega

/-- After exponent trit `2`, the affine coordinate tail is exactly `peel2`. -/
theorem tail3_affineOrbit_three_mul_add_two (q : Nat) :
    tail3 (affineOrbit (3*q+2)) = peel2 (affineOrbit q) := by
  unfold tail3
  rw [affineOrbit_three_mul_add_two]
  omega

/-- Exact first exponent-trit classifier, branch `0`. -/
theorem noCommonTwo_three_mul_iff (q : Nat) :
    (¬ CommonTwo (3*q)) ↔
      BadChannel 0 (peel0 (affineOrbit q)) := by
  rw [noCommonTwo_low_trit_branch]
  simp [tail3_affineOrbit_three_mul]

/-- Exact first exponent-trit classifier, branch `1`. -/
theorem noCommonTwo_three_mul_add_one_iff (q : Nat) :
    (¬ CommonTwo (3*q+1)) ↔
      BadChannel 1 (peel1 (affineOrbit q)) := by
  have hmod : (3*q+1) % 3 = 1 := by omega
  rw [noCommonTwo_low_trit_branch]
  rw [tail3_affineOrbit_three_mul_add_one]
  simp [hmod]

/-- Exact first exponent-trit classifier, branch `2`. -/
theorem noCommonTwo_three_mul_add_two_iff (q : Nat) :
    (¬ CommonTwo (3*q+2)) ↔
      BadChannel 3 (peel2 (affineOrbit q)) := by
  have hmod : (3*q+2) % 3 = 2 := by omega
  rw [noCommonTwo_low_trit_branch]
  rw [tail3_affineOrbit_three_mul_add_two]
  simp [hmod]

/-- The low ternary digit of the `0` peel is inherited from its input. -/
theorem peel0_mod_three (x : Nat) : peel0 x % 3 = x % 3 := by
  simp [peel0, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- The low ternary digit of the `1` peel is also inherited from its input. -/
theorem peel1_mod_three (x : Nat) : peel1 x % 3 = x % 3 := by
  rw [peel1_eq_four_peel0]
  simp [Nat.mul_mod, peel0_mod_three]

/-- The low ternary digit of the `2` peel is the successor of the input trit. -/
theorem peel2_mod_three (x : Nat) : peel2 x % 3 = (x + 1) % 3 := by
  rw [peel2_eq_four_peel1_add_one]
  simp [Nat.add_mod, Nat.mul_mod, peel1_mod_three]

/-- Therefore the second automaton read after exponent branch `0` is exactly
    the next ternary exponent trit. -/
theorem lowDigit_peel0_affineOrbit (q : Nat) :
    lowDigit (peel0 (affineOrbit q)) = q % 3 := by
  unfold lowDigit
  rw [peel0_mod_three, affineOrbit_mod_three]

/-- The same is true after exponent branch `1`. -/
theorem lowDigit_peel1_affineOrbit (q : Nat) :
    lowDigit (peel1 (affineOrbit q)) = q % 3 := by
  unfold lowDigit
  rw [peel1_mod_three, affineOrbit_mod_three]

/-- Branch `2` twists the next automaton read by one. -/
theorem lowDigit_peel2_affineOrbit (q : Nat) :
    lowDigit (peel2 (affineOrbit q)) = (q + 1) % 3 := by
  unfold lowDigit
  rw [peel2_mod_three]
  calc
    (affineOrbit q + 1) % 3 = (affineOrbit q % 3 + 1 % 3) % 3 := Nat.add_mod _ _ _
    _ = (q % 3 + 1 % 3) % 3 := by rw [affineOrbit_mod_three]
    _ = (q + 1) % 3 := (Nat.add_mod q 1 3).symm

/-- A bad exponent in branch `0` cannot have second ternary trit `2`.
    State `0` has only `0` and `1` as surviving next reads. -/
theorem noCommonTwo_three_mul_forces_q_mod_three_ne_two
    (q : Nat) (hNo : ¬ CommonTwo (3*q)) : q % 3 ≠ 2 := by
  intro hq
  have hbad : BadChannel 0 (peel0 (affineOrbit q)) :=
    (noCommonTwo_three_mul_iff q).mp hNo
  rcases (badChannel_zero_iff _).mp hbad with h0 | h1
  · have hd := h0.1
    rw [lowDigit_peel0_affineOrbit q, hq] at hd
    omega
  · have hd := h1.1
    rw [lowDigit_peel0_affineOrbit q, hq] at hd
    omega

/-- Positive form of the previous survivor law: exponent suffix `20` in
    least-significant-first ternary order is killed immediately by the direct
    affine automaton, hence a genuine common-two row exists. -/
theorem commonTwo_three_mul_of_q_mod_three_eq_two
    (q : Nat) (hq : q % 3 = 2) : CommonTwo (3*q) := by
  by_contra hNo
  exact noCommonTwo_three_mul_forces_q_mod_three_ne_two q hNo hq

/-- A bad exponent in branch `2` cannot make the twisted second read equal `2`.
    State `3` has only `0` and `1` as surviving next reads. -/
theorem noCommonTwo_three_mul_add_two_forces_next_ne_two
    (q : Nat) (hNo : ¬ CommonTwo (3*q+2)) : (q+1) % 3 ≠ 2 := by
  intro hq
  have hbad : BadChannel 3 (peel2 (affineOrbit q)) :=
    (noCommonTwo_three_mul_add_two_iff q).mp hNo
  rcases (badChannel_three_iff _).mp hbad with h0 | h1
  · have hd := h0.1
    rw [lowDigit_peel2_affineOrbit q, hq] at hd
    omega
  · have hd := h1.1
    rw [lowDigit_peel2_affineOrbit q, hq] at hd
    omega

/-- Positive branch-`2` killing law.  If the next exponent trit is `1`, the
    twisted affine read becomes `2`, so state `3` terminates in a common-two
    witness. -/
theorem commonTwo_three_mul_add_two_of_q_mod_three_eq_one
    (q : Nat) (hq : q % 3 = 1) : CommonTwo (3*q+2) := by
  by_contra hNo
  have hnext : (q+1) % 3 = 2 := by
    calc
      (q+1) % 3 = (q % 3 + 1 % 3) % 3 := Nat.add_mod q 1 3
      _ = 2 := by rw [hq]; norm_num
  exact noCommonTwo_three_mul_add_two_forces_next_ne_two q hNo hnext

#check tail3_affineOrbit_three_mul
#check tail3_affineOrbit_three_mul_add_one
#check tail3_affineOrbit_three_mul_add_two
#check noCommonTwo_three_mul_iff
#check noCommonTwo_three_mul_add_one_iff
#check noCommonTwo_three_mul_add_two_iff
#check lowDigit_peel0_affineOrbit
#check lowDigit_peel1_affineOrbit
#check lowDigit_peel2_affineOrbit
#check noCommonTwo_three_mul_forces_q_mod_three_ne_two
#check commonTwo_three_mul_of_q_mod_three_eq_two
#check noCommonTwo_three_mul_add_two_forces_next_ne_two
#check commonTwo_three_mul_add_two_of_q_mod_three_eq_one
#print axioms noCommonTwo_three_mul_iff
#print axioms noCommonTwo_three_mul_add_one_iff
#print axioms noCommonTwo_three_mul_add_two_iff
#print axioms noCommonTwo_three_mul_forces_q_mod_three_ne_two
#print axioms commonTwo_three_mul_of_q_mod_three_eq_two
#print axioms noCommonTwo_three_mul_add_two_forces_next_ne_two
#print axioms commonTwo_three_mul_add_two_of_q_mod_three_eq_one

end GSTFourPowerAffinePeelClassifier
