import GSTGraphV2CanonicalExperiment

/-!
# GST Graph V2 — macro radix-surface experiment

This layer kernelizes the exact macro-rotation discovery from the Sol V2
ledgers.  The first base-4 cyclic rotation is proved to read the *physical*
parent boundary.  Later rotations are intentionally not promoted to physical
transport.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Experiment

/-- The single shared information integer in its direct affine form. -/
def sharedState (A z T q : Nat) : Nat :=
  affineCarry (4*A) (1 + 4*z) T q

/-- Direct affine shared state equals the bottom `D + 4Z` reading. -/
theorem shared_state_exact (A z T q : Nat) :
    sharedState A z T q =
      (frame A z T q).parentSeedCarry +
        4 * (frame A z T q).lowAffineCarry := by
  let M := 3^q
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.pow_pos (by decide)
  let Y := z + A*(T % M)
  have hmodY : Y % M = (z + A*T) % M := by
    dsimp [Y, M]
    simp [Nat.add_mod, Nat.mul_mod]
  have hdiv := affine_tail_div_decomposition 1 4 Y q
  have hYdiv : Y / M = affineCarry A z T q := by
    dsimp [Y, M, affineCarry]
  have hparent :
      affineCarry 4 1 Y q = affineCarry 4 1 (z + A*T) q := by
    unfold affineCarry
    dsimp [M] at hmodY
    rw [hmodY]
  calc
    sharedState A z T q = (1 + 4*Y) / 3^q := by
      unfold sharedState affineCarry
      dsimp [Y, M]
      congr 1
      ring
    _ = affineCarry 4 1 Y q + 4 * (Y / 3^q) := hdiv
    _ = affineCarry 4 1 (z + A*T) q +
          4 * affineCarry A z T q := by
      dsimp [M] at hYdiv
      rw [hparent, hYdiv]
    _ = (frame A z T q).parentSeedCarry +
          4 * (frame A z T q).lowAffineCarry := by
      rfl

/-- The shared state obeys literal vertical long division by three. -/
theorem shared_state_forward (A z T q : Nat) :
    sharedState A z T (q+1) =
      (sharedState A z T q + (4*A) * digit T q) / 3 := by
  simp only [sharedState, affineCarry, digit, Nat.pow_succ]
  have hp : 0 < 3^q := Nat.pow_pos (by decide)
  have hsplit : T % (3^q * 3) =
      T % 3^q + 3^q * (T / 3^q % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit, Nat.mul_add]
  rw [show (4*A) * (3^q * (T / 3^q % 3)) =
      3^q * ((4*A) * (T / 3^q % 3)) by ac_rfl]
  rw [show
      1 + 4*z + ((4*A) * (T % 3^q) +
        3^q * ((4*A) * (T / 3^q % 3))) =
      (1 + 4*z + (4*A) * (T % 3^q)) +
        3^q * ((4*A) * (T / 3^q % 3)) by ring]
  rw [← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ hp]

/-- Parent seed and vertical affine carry are bottom base-4 digit/quotient. -/
theorem shared_state_bottom_coordinates (A z T q : Nat) :
    sharedState A z T q % 4 = (frame A z T q).parentSeedCarry ∧
      sharedState A z T q / 4 = (frame A z T q).lowAffineCarry := by
  have hD : (frame A z T q).parentSeedCarry < 4 := by
    have h := affine_carry_lt_multiplier 4 1 (z + A*T) q
      (by decide) (by decide)
    simpa [frame] using h
  have hS := shared_state_exact A z T q
  constructor
  · rw [hS, Nat.add_mod, Nat.mul_mod]
    simp [Nat.mod_eq_of_lt hD]
  · rw [hS]
    have h4 : 0 < (4:Nat) := by decide
    rw [Nat.add_mul_div_left _ _ h4]
    rw [Nat.div_eq_of_lt hD]
    simp

/-- Child carry is the top base-A quotient of the same information integer. -/
theorem shared_state_child_coordinate
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    sharedState A z T q / A = (frame A z T q).childCarry := by
  have hEq := frame_shared_conservation A z T q
  have hW : (frame A z T q).latentCarry < A := by
    simpa [frame] using
      affine_carry_lt_multiplier A (1 + 4*z) (4*T) q hA hz1
  have hShared := shared_state_exact A z T q
  rw [hShared]
  rw [← hEq]
  have hshape :
      (frame A z T q).latentCarry + A * (frame A z T q).childCarry =
        A * (frame A z T q).childCarry + (frame A z T q).latentCarry := by
    omega
  rw [hshape]
  exact (Nat.mul_add_div A (frame A z T q).childCarry
    (frame A z T q).latentCarry).trans (by
      rw [Nat.div_eq_of_lt hW]
      simp [hA])

/-- If `A ≡ 1 mod 3`, the parent digit is read from vertical quotient + child digit. -/
theorem parent_digit_from_information
    (A z T q : Nat) (hA3 : A % 3 = 1) :
    (frame A z T q).parentDigit =
      ((frame A z T q).lowAffineCarry +
        (frame A z T q).childDigit) % 3 := by
  have htail := affine_tail_div_decomposition z A T q
  unfold digit at htail ⊢
  simp only [frame]
  rw [htail]
  have hmul : (A * (T / 3^q)) % 3 = T / 3^q % 3 := by
    calc
      (A * (T / 3^q)) % 3 =
          ((A % 3) * ((T / 3^q) % 3)) % 3 := Nat.mul_mod A (T / 3^q) 3
      _ = (T / 3^q) % 3 := by simp [hA3]
  rw [Nat.add_mod, hmul]
  simp

/-- Cyclic rotation of the `N+1` base-4 carry word, with `A=4^N`. -/
def macroRotate (A S : Nat) : Nat := S / 4 + A * (S % 4)

structure MacroState where
  carrier : Nat
  phaseDigit : Nat
  deriving Repr, DecidableEq

/-- One global macro re-coordinate step. -/
def macroStep (A : Nat) (m : MacroState) : MacroState :=
  {
    carrier := macroRotate A m.carrier
    phaseDigit := (m.carrier / 4 + m.phaseDigit) % 3
  }

/-- Macro index zero is the physical child boundary. -/
def childMacroState (A z T q : Nat) : MacroState :=
  {
    carrier := sharedState A z T q
    phaseDigit := (frame A z T q).childDigit
  }

/-- The first macro rotation has exactly the physical parent carry and digit. -/
theorem first_macro_step_is_physical_parent
    (A z T q : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hA3 : A % 3 = 1) :
    let m1 := macroStep A (childMacroState A z T q)
    m1.carrier / A = (frame A z T q).parentSeedCarry ∧
      m1.phaseDigit = (frame A z T q).parentDigit := by
  dsimp only [macroStep, childMacroState]
  have hb := shared_state_bottom_coordinates A z T q
  have hZ : (frame A z T q).lowAffineCarry < A := by
    have hz : z < A := by omega
    simpa [frame] using affine_carry_lt_multiplier A z T q hA hz
  have hcarrier :
      macroRotate A (sharedState A z T q) =
        (frame A z T q).lowAffineCarry +
          A * (frame A z T q).parentSeedCarry := by
    unfold macroRotate
    rw [hb.1, hb.2]
  constructor
  · rw [hcarrier]
    have hApos : 0 < A := hA
    have hshape :
        (frame A z T q).lowAffineCarry +
            A * (frame A z T q).parentSeedCarry =
          A * (frame A z T q).parentSeedCarry +
            (frame A z T q).lowAffineCarry := by omega
    rw [hshape]
    exact (Nat.mul_add_div A (frame A z T q).parentSeedCarry
      (frame A z T q).lowAffineCarry).trans (by
        rw [Nat.div_eq_of_lt hZ]
        simp [hApos])
  · rw [hb.2]
    exact (parent_digit_from_information A z T q hA3).symm

/-- Happy predicate for a macro boundary reading. -/
def MacroHappy (A : Nat) (m : MacroState) : Prop :=
  m.phaseDigit = 2 ∧ (m.carrier / A = 0 ∨ m.carrier / A = 3)

/-- Macro index zero is Happy exactly when the child GST cell is Happy. -/
theorem child_macro_happy_iff
    (A z T q : Nat) (hA : 0 < A) (hz1 : 1 + 4*z < A) :
    MacroHappy A (childMacroState A z T q) ↔
      digit T q = 2 ∧ (carry T q = 0 ∨ carry T q = 3) := by
  unfold MacroHappy childMacroState
  rw [shared_state_child_coordinate A z T q hA hz1]
  rfl

/-- Macro index one is Happy exactly when the physical parent row is Happy. -/
theorem parent_macro_happy_iff
    (A z T q : Nat)
    (hA : 0 < A)
    (hz1 : 1 + 4*z < A)
    (hA3 : A % 3 = 1) :
    MacroHappy A (macroStep A (childMacroState A z T q)) ↔
      (frame A z T q).parentDigit = 2 ∧
        ((frame A z T q).parentSeedCarry = 0 ∨
         (frame A z T q).parentSeedCarry = 3) := by
  have hp := first_macro_step_is_physical_parent A z T q hA hz1 hA3
  unfold MacroHappy
  rw [hp.1, hp.2]

/-- Exact V2 research target after the macro physical/subspace distinction is fixed.
A canonical origin-driven vertical evolution may route a child Happy state through
alternate macro indices, but physical macro index one must eventually become Happy. -/
def MacroRoutingTarget
    (A z T : Nat) : Prop :=
  (∃ q, MacroHappy A (childMacroState A z T q)) →
    ∃ q, MacroHappy A (macroStep A (childMacroState A z T q))

end GSTGraphV2Experiment
