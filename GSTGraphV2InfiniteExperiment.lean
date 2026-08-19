import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Experiment

/-!
# Infinite-information experiment

This file isolates the exact handwritten `I ≠ BIG1` branch used by the
prefix-one phase-crossing surgery.  It proves the rigid microscopic statement:
a legal x2 information path that starts at BIG2 either hits BIG1 at a finite
position or remains BIG2 at every finite position.
-/

/-- One microscopic multiply-by-two/base-three information output. -/
def binaryInfoOutput (a d : Nat) : Nat := (a + 2*d) % 3

/-- A legal finite microscopic information path. -/
def BinaryInfoPath (a d : Nat → Nat) (K : Nat) : Prop :=
  (∀ i, i < K → a i < 2) ∧
  (∀ i, i ≤ K → d i < 3) ∧
  (∀ i, i < K → binaryInfoOutput (a i) (d i) = d (i+1))

/-- At BIG2, avoiding BIG1 on the next information vertex forces the unique
binary carry bit one and preserves BIG2. -/
theorem binary_big2_step_of_next_ne_big1
    (a e : Nat) (ha : a < 2) (he : e < 3) (he1 : e ≠ 1)
    (hstep : binaryInfoOutput a 2 = e) :
    a = 1 ∧ e = 2 := by
  have hac : a = 0 ∨ a = 1 := by omega
  rcases hac with h0 | h1
  · subst a
    norm_num [binaryInfoOutput] at hstep
    omega
  · subst a
    norm_num [binaryInfoOutput] at hstep
    exact ⟨rfl, hstep.symm⟩

/-- If a legal path starts at BIG2 and contains no BIG1 through depth K, every
finite information vertex through K is BIG2. -/
theorem binary_big1_free_path_forces_all_big2
    (a d : Nat → Nat) (K : Nat)
    (hpath : BinaryInfoPath a d K)
    (h0 : d 0 = 2)
    (hclear : ∀ i, i ≤ K → d i ≠ 1) :
    ∀ i, i ≤ K → d i = 2 := by
  intro i hi
  induction i with
  | zero => exact h0
  | succ i ih =>
      have hiK : i < K := by omega
      have hdi : d i = 2 := ih (by omega)
      have ha : a i < 2 := hpath.1 i hiK
      have he : d (i+1) < 3 := hpath.2.1 (i+1) (by omega)
      have he1 : d (i+1) ≠ 1 := hclear (i+1) (by omega)
      have hstep : binaryInfoOutput (a i) 2 = d (i+1) := by
        simpa [hdi] using hpath.2.2 i hiK
      exact (binary_big2_step_of_next_ne_big1
        (a i) (d (i+1)) ha he he1 hstep).2

/-- Exact finite dichotomy behind the handwritten operator: starting from BIG2,
either BIG1 occurs at a concrete finite information index, or BIG2 occupies
every vertex through the chosen horizon. -/
theorem binary_path_big1_or_all_big2
    (a d : Nat → Nat) (K : Nat)
    (hpath : BinaryInfoPath a d K)
    (h0 : d 0 = 2) :
    (∃ i, i ≤ K ∧ d i = 1) ∨
      (∀ i, i ≤ K → d i = 2) := by
  by_cases hbig1 : ∃ i, i ≤ K ∧ d i = 1
  · exact Or.inl hbig1
  · right
    apply binary_big1_free_path_forces_all_big2 a d K hpath h0
    intro i hi hi1
    exact hbig1 ⟨i, hi, hi1⟩

/-- Boss's `i = N` endpoint collapse in its exact finite form.  If the path
starts at BIG2 but the chosen finite information horizon is zero, a BIG1
crossing must occur somewhere before or at that horizon. -/
theorem binary_big2_to_zero_forces_big1
    (a d : Nat → Nat) (K : Nat)
    (hpath : BinaryInfoPath a d K)
    (h0 : d 0 = 2)
    (hK : d K = 0) :
    ∃ i, i ≤ K ∧ d i = 1 := by
  rcases binary_path_big1_or_all_big2 a d K hpath h0 with hbig1 | hall
  · exact hbig1
  · have htwo : d K = 2 := hall K (by omega)
    omega

/-- Infinite form: excluding BIG1 at every natural information position forces
BIG2 at every natural information position. -/
theorem binary_infinite_big1_free_forces_big2
    (a d : Nat → Nat)
    (hlegalCarry : ∀ i, a i < 2)
    (hlegalDigit : ∀ i, d i < 3)
    (hstep : ∀ i, binaryInfoOutput (a i) (d i) = d (i+1))
    (h0 : d 0 = 2)
    (hclear : ∀ i, d i ≠ 1) :
    ∀ i, d i = 2 := by
  intro i
  have hpath : BinaryInfoPath a d i := by
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      exact hlegalCarry j
    · intro j hj
      exact hlegalDigit j
    · intro j hj
      exact hstep j
  exact binary_big1_free_path_forces_all_big2 a d i hpath h0
    (fun j _ => hclear j) i (by omega)

/-! ## Physical x4 classification at a bad BIG2 cell -/

def microHighBit (C : Nat) : Nat := C / 2
def microLowBit (C : Nat) : Nat := C % 2
def firstMicroMass (C d : Nat) : Nat := microHighBit C + 2*d
def firstMicroOutput (C d : Nat) : Nat := firstMicroMass C d % 3
def secondMicroMass (C d : Nat) : Nat := microLowBit C + 2*firstMicroOutput C d
def secondMicroOutput (C d : Nat) : Nat := secondMicroMass C d % 3

/-- At a physical BIG2 input, excluding both Happy carries 0 and 3 leaves
exactly two ALT-minus escape cells.  They expose BIG1 on one of the two
microscopic information vertices; there is no third bad BIG2 orientation. -/
theorem physical_bad_big2_exact_two_escapes
    (C : Nat) (hC : C < 4) (hbad : C ≠ 0 ∧ C ≠ 3) :
    (C = 1 ∧
      firstMicroMass C 2 = 4 ∧ secondMicroMass C 2 = 3 ∧
      firstMicroOutput C 2 = 1 ∧ secondMicroOutput C 2 = 0) ∨
    (C = 2 ∧
      firstMicroMass C 2 = 5 ∧ secondMicroMass C 2 = 4 ∧
      firstMicroOutput C 2 = 2 ∧ secondMicroOutput C 2 = 1) := by
  have hcases : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact False.elim (hbad.1 h0)
  · subst C
    left
    norm_num [firstMicroMass, secondMicroMass, firstMicroOutput,
      secondMicroOutput, microHighBit, microLowBit]
  · subst C
    right
    norm_num [firstMicroMass, secondMicroMass, firstMicroOutput,
      secondMicroOutput, microHighBit, microLowBit]
  · exact False.elim (hbad.2 h3)

/-- Therefore every bad physical BIG2 cell necessarily crosses BIG1 within
its two microscopic x2 layers. -/
theorem physical_bad_big2_forces_big1_micro_vertex
    (C : Nat) (hC : C < 4) (hbad : C ≠ 0 ∧ C ≠ 3) :
    firstMicroOutput C 2 = 1 ∨ secondMicroOutput C 2 = 1 := by
  rcases physical_bad_big2_exact_two_escapes C hC hbad with h1 | h2
  · exact Or.inl h1.2.2.2.1
  · exact Or.inr h2.2.2.2.2

/-! ## Real integer x2 path constructor -/

/-- Incoming binary carry at ternary row `p` when multiplying `R` by two. -/
def binaryCarryAt (R p : Nat) : Nat :=
  (2 * (R % 3^p)) / 3^p

/-- Ordinary ternary input digit at row `p`. -/
def ternaryDigitAt (R p : Nat) : Nat := R / 3^p % 3

/-- Every physical x2 carry is a legal bit. -/
theorem binaryCarryAt_lt_two (R p : Nat) : binaryCarryAt R p < 2 := by
  unfold binaryCarryAt
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hr : R % 3^p < 3^p := Nat.mod_lt _ hp
  have hmul : 2 * (R % 3^p) < 3^p * 2 := by omega
  exact Nat.div_lt_of_lt_mul hmul

/-- Exact physical x2 output digit. -/
theorem ternaryDigitAt_mul_two
    (R p : Nat) :
    ternaryDigitAt (2*R) p =
      binaryInfoOutput (binaryCarryAt R p) (ternaryDigitAt R p) := by
  unfold ternaryDigitAt binaryCarryAt binaryInfoOutput
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  have hsplit :
      (2*R) / 3^p =
        (2 * (R % 3^p)) / 3^p + 2 * (R / 3^p) := by
    calc
      (2*R) / 3^p =
          (2 * (R % 3^p + 3^p * (R / 3^p))) / 3^p := by
            rw [Nat.mod_add_div]
      _ = (2 * (R % 3^p) + 3^p * (2 * (R / 3^p))) / 3^p := by
            congr 1
            ring
      _ = (2 * (R % 3^p)) / 3^p + 2 * (R / 3^p) := by
            rw [Nat.add_mul_div_left _ _ hp]
  rw [hsplit]
  have hqmod :
      (2 * (R / 3^p)) % 3 =
        (2 * (R / 3^p % 3)) % 3 := by
    simpa only [Nat.mod_mod] using
      (Nat.mul_mod 2 (R / 3^p) 3)
  calc
    ((2 * (R % 3^p)) / 3^p + 2 * (R / 3^p)) % 3 =
        (((2 * (R % 3^p)) / 3^p) % 3 +
          (2 * (R / 3^p)) % 3) % 3 :=
      Nat.add_mod _ _ 3
    _ = ((((2 * (R % 3^p)) / 3^p) % 3) +
          (2 * (R / 3^p % 3)) % 3) % 3 := by rw [hqmod]
    _ = ((2 * (R % 3^p)) / 3^p +
          2 * (R / 3^p % 3)) % 3 := by
      symm
      exact Nat.add_mod _ _ 3

/-- The actual powers-of-two orbit at one ternary row is a legal microscopic
bridge path, with no abstract transition assumption. -/
theorem physical_binary_orbit_is_path
    (R p K : Nat) :
    BinaryInfoPath
      (fun i => binaryCarryAt (2^i * R) p)
      (fun i => ternaryDigitAt (2^i * R) p) K := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact binaryCarryAt_lt_two (2^i * R) p
  · intro i hi
    unfold ternaryDigitAt
    exact Nat.mod_lt _ (by decide)
  · intro i hi
    have hstep := ternaryDigitAt_mul_two (2^i * R) p
    have hpows : 2 * (2^i * R) = 2^(i+1) * R := by
      rw [Nat.pow_succ]
      ac_rfl
    rw [hpows] at hstep
    exact hstep.symm

/-- Concrete BIG-N/finite-horizon form: if a real powers-of-two information
orbit starts at BIG2 and is zero at finite depth K, it must physically cross
BIG1 at some intermediate microscopic phase. -/
theorem physical_binary_big2_to_zero_forces_big1
    (R p K : Nat)
    (h0 : ternaryDigitAt R p = 2)
    (hK : ternaryDigitAt (2^K * R) p = 0) :
    ∃ i, i ≤ K ∧ ternaryDigitAt (2^i * R) p = 1 := by
  have hpath := physical_binary_orbit_is_path R p K
  exact binary_big2_to_zero_forces_big1
    (fun i => binaryCarryAt (2^i * R) p)
    (fun i => ternaryDigitAt (2^i * R) p)
    K hpath (by simpa using h0) (by simpa using hK)

end GSTGraphV2Experiment
