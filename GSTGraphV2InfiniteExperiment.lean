import GSTGraphV2CanonicalExperiment

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

end GSTGraphV2Experiment
