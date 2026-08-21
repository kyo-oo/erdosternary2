import GSTV2InfiniteCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTV2

/-!
# GST V2 all-depth coupled information transport

This is the production transport layer between the finite natural child word
and the parent affine information word.  Nothing terminates here: the state is
iterated on every `K : Nat`.  When a finite child tail eventually becomes
zero, its information has already been transferred into the other coordinates
of the exact shared-state equation.

The local CREATE / DESTROY / SURVIVE vocabulary is deliberately absent from
this layer.  This file proves the stronger representation-independent fact:
the same shared information equation survives every natural observation
step.
-/

/-- Seeded x4 carry attached to an affine information word. -/
def affineCarry (D X k : Nat) : Nat :=
  (D + 4 * (X % 3^k)) / 3^k

/-- The ordinary x4 carry of a finite child word. -/
def naturalCarry (Y k : Nat) : Nat :=
  (4 * (Y % 3^k)) / 3^k

/-- Exact seeded x4 recurrence at every natural coordinate. -/
theorem affineCarry_forward (D X k : Nat) :
    affineCarry D X (k+1) =
      cellNextCarry (affineCarry D X k) (digit X k) := by
  simp only [affineCarry, digit, cellNextCarry, cellMass, Nat.pow_succ]
  have hk : 0 < 3^k := Nat.pow_pos (by decide)
  have hsplit : X % (3^k * 3) =
      X % 3^k + 3^k * (X / 3^k % 3) := by
    rw [Nat.mod_mul]
  rw [hsplit]
  have hshape :
      D + 4 * (X % 3^k + 3^k * (X / 3^k % 3)) =
        (D + 4 * (X % 3^k)) +
          3^k * (4 * (X / 3^k % 3)) := by ring
  rw [hshape, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_left _ _ hk]

/-- Exact ordinary x4 recurrence at every natural coordinate. -/
theorem naturalCarry_forward (Y k : Nat) :
    naturalCarry Y (k+1) =
      cellNextCarry (naturalCarry Y k) (digit Y k) := by
  simpa [naturalCarry, affineCarry] using affineCarry_forward 0 Y k

/-- Exact ternary digit reindexing. -/
theorem digit_shift (Y q j : Nat) :
    digit Y (q+j) = digit (Y / 3^q) j := by
  simp only [digit]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- One coupled state.  `parentSeed,parentOffset` are the low endpoint;
`childResidue,childCarry` are the high endpoint; `childTail` is the still
unconsumed natural-origin information. -/
structure CoupledState where
  parentSeed : Nat
  parentOffset : Nat
  childResidue : Nat
  childCarry : Nat
  childTail : Nat
  deriving Repr

/-- The parent affine information word represented by a coupled state. -/
def CoupledState.parentWord (A : Nat) (st : CoupledState) : Nat :=
  st.parentOffset + A * st.childTail

/-- The exact two-endpoint information equation. -/
def CoupledInvariant (A : Nat) (st : CoupledState) : Prop :=
  st.parentSeed + 4 * st.parentOffset =
      st.childResidue + A * st.childCarry ∧
    st.childResidue < A

/-- One information-transport step.  The child emits its next ternary digit;
the parent affine word emits the corresponding represented digit.  Both
endpoint carries and both finite remainders are updated, while `A` is fixed. -/
def coupledStep (A : Nat) (st : CoupledState) : CoupledState :=
  let r := st.childTail % 3
  let e := (st.parentOffset + A*r) % 3
  let u := cellOutput st.childCarry r
  {
    parentSeed := cellNextCarry st.parentSeed e
    parentOffset := (st.parentOffset + A*r) / 3
    childResidue := (st.childResidue + A*u) / 3
    childCarry := cellNextCarry st.childCarry r
    childTail := st.childTail / 3
  }

/-- The low endpoint regenerates exactly. -/
theorem coupled_low_regenerates
    (A D Z r : Nat) :
    (D + 4*Z + 4*A*r) / 3 =
      cellNextCarry D ((Z + A*r) % 3) +
        4 * ((Z + A*r) / 3) := by
  let E := Z + A*r
  have hE : E = E % 3 + 3*(E/3) := by
    have h := Nat.mod_add_div E 3
    omega
  have hshape : D + 4*Z + 4*A*r = D + 4*E := by
    dsimp [E]
    ring
  rw [hshape, hE]
  have hnum :
      D + 4 * (E % 3 + 3 * (E / 3)) =
        (D + 4*(E%3)) + 3*(4*(E/3)) := by ring
  rw [hnum]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  rfl

/-- The high endpoint regenerates by the same exact quotient law. -/
theorem coupled_high_regenerates
    (A W C r : Nat) :
    (W + A*C + 4*A*r) / 3 =
      (W + A*cellOutput C r) / 3 +
        A * cellNextCarry C r := by
  let U := C + 4*r
  have hU : U = U % 3 + 3*(U/3) := by
    have h := Nat.mod_add_div U 3
    omega
  have hshape0 : W + A*C + 4*A*r = W + A*U := by
    dsimp [U]
    ring
  rw [hshape0, hU]
  have hshape1 :
      W + A*(U % 3 + 3*(U/3)) =
        (W + A*(U%3)) + 3*(A*(U/3)) := by ring
  rw [hshape1]
  have h3 : 0 < (3:Nat) := by decide
  rw [Nat.add_mul_div_left _ _ h3]
  simp [cellOutput, cellNextCarry, cellMass, U]

/-- The high finite remainder stays inside the same horizontal world. -/
theorem coupled_high_residue_lt
    (A W C r : Nat) (hA : 0 < A) (hW : W < A) :
    (W + A*cellOutput C r) / 3 < A := by
  have hu : cellOutput C r < 3 := by
    unfold cellOutput
    exact Nat.mod_lt _ (by decide)
  have hu1 : cellOutput C r + 1 ≤ 3 := Nat.succ_le_of_lt hu
  have hnum : W + A*cellOutput C r < 3*A := by
    calc
      W + A*cellOutput C r < A + A*cellOutput C r :=
        Nat.add_lt_add_right hW _
      _ = A * (cellOutput C r + 1) := by ring
      _ ≤ A*3 := Nat.mul_le_mul_left A hu1
      _ = 3*A := by ring
  exact Nat.div_lt_of_lt_mul hnum

/-- One step preserves the exact shared information equation. -/
theorem coupledStep_preserves_invariant
    (A : Nat) (st : CoupledState)
    (hA : 0 < A) (hInv : CoupledInvariant A st) :
    CoupledInvariant A (coupledStep A st) := by
  rcases hInv with ⟨hEq, hW⟩
  unfold CoupledInvariant coupledStep
  dsimp only
  let r := st.childTail % 3
  have hlow := coupled_low_regenerates
    A st.parentSeed st.parentOffset r
  have hhigh := coupled_high_regenerates
    A st.childResidue st.childCarry r
  have hEq' :
      cellNextCarry st.parentSeed ((st.parentOffset + A*r) % 3) +
          4*((st.parentOffset + A*r)/3) =
        (st.childResidue + A*cellOutput st.childCarry r)/3 +
          A*cellNextCarry st.childCarry r := by
    rw [← hlow, ← hhigh]
    rw [hEq]
  refine ⟨?_, ?_⟩
  · simpa [r] using hEq'
  · exact coupled_high_residue_lt A st.childResidue st.childCarry r hA hW

/-- One transport step consumes exactly one ternary digit of the child tail
without losing the remaining parent affine word. -/
theorem coupledStep_parentWord_div_three
    (A : Nat) (st : CoupledState) :
    (coupledStep A st).parentWord A = st.parentWord A / 3 := by
  unfold CoupledState.parentWord coupledStep
  dsimp only
  let r := st.childTail % 3
  have hY : st.childTail = r + 3*(st.childTail/3) := by
    dsimp [r]
    have h := Nat.mod_add_div st.childTail 3
    omega
  have h3 : 0 < (3:Nat) := by decide
  calc
    (st.parentOffset + A*r) / 3 + A*(st.childTail/3) =
        ((st.parentOffset + A*r) + 3*(A*(st.childTail/3))) / 3 := by
      rw [Nat.add_mul_div_left _ _ h3]
    _ = (st.parentOffset + A*st.childTail) / 3 := by
      congr 1
      calc
        (st.parentOffset + A*r) + 3*(A*(st.childTail/3)) =
            st.parentOffset + A*(r + 3*(st.childTail/3)) := by ring
        _ = st.parentOffset + A*st.childTail := by rw [← hY]

/-- The all-Nat coupled orbit.  `K` is an observation depth, not a termination
bound. -/
def coupledOrbit (A : Nat) (initial : CoupledState) : Nat → CoupledState
  | 0 => initial
  | K+1 => coupledStep A (coupledOrbit A initial K)

/-- Exact shared information conservation at every natural observation depth. -/
theorem coupledOrbit_invariant_all
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    ∀ K, CoupledInvariant A (coupledOrbit A initial K) := by
  intro K
  induction K with
  | zero => exact h0
  | succ K ih =>
      exact coupledStep_preserves_invariant A (coupledOrbit A initial K) hA ih

/-- The visible child tail at depth `K` is exactly the original natural tail
shifted by `K` ternary coordinates. -/
theorem coupledOrbit_childTail_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K, (coupledOrbit A initial K).childTail = initial.childTail / 3^K := by
  intro K
  induction K with
  | zero => simp [coupledOrbit]
  | succ K ih =>
      rw [coupledOrbit]
      change (coupledOrbit A initial K).childTail / 3 = _
      rw [ih, Nat.pow_succ, ← Nat.div_div_eq_div_mul]

/-- The represented parent word at every depth is exactly the corresponding
ternary suffix of the original parent word. -/
theorem coupledOrbit_parentWord_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      (coupledOrbit A initial K).parentWord A =
        initial.parentWord A / 3^K := by
  intro K
  induction K with
  | zero => simp [coupledOrbit]
  | succ K ih =>
      rw [coupledOrbit, coupledStep_parentWord_div_three, ih,
        Nat.pow_succ, ← Nat.div_div_eq_div_mul]

/-- Closed form for the low parent offset at every natural observation depth.
It is the quotient of the initial offset plus the multiplier times the exact
visible child prefix; no information is discarded when the child Future is
shifted. -/
theorem coupledOrbit_parentOffset_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K,
      (coupledOrbit A initial K).parentOffset =
        (initial.parentOffset + A * (initial.childTail % 3^K)) / 3^K := by
  intro K
  let P := 3^K
  have hP : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos (by decide)
  have hTail := coupledOrbit_childTail_exact A initial K
  have hWord := coupledOrbit_parentWord_exact A initial K
  have hsplit :
      initial.childTail = initial.childTail % P +
        P * (initial.childTail / P) := by
    have h := Nat.mod_add_div initial.childTail P
    omega
  have hnum :
      initial.parentOffset + A * initial.childTail =
        (initial.parentOffset + A * (initial.childTail % P)) +
          P * (A * (initial.childTail / P)) := by
    calc
      initial.parentOffset + A * initial.childTail =
          initial.parentOffset +
            A * (initial.childTail % P + P * (initial.childTail / P)) := by
        rw [← hsplit]
      _ = (initial.parentOffset + A * (initial.childTail % P)) +
          P * (A * (initial.childTail / P)) := by ring
  have hdiv :
      (initial.parentOffset + A * initial.childTail) / P =
        (initial.parentOffset + A * (initial.childTail % P)) / P +
          A * (initial.childTail / P) := by
    rw [hnum, Nat.add_mul_div_left _ _ hP]
  unfold CoupledState.parentWord at hWord
  change (coupledOrbit A initial K).childTail =
    initial.childTail / P at hTail
  change (coupledOrbit A initial K).parentOffset +
      A * (coupledOrbit A initial K).childTail =
    (initial.parentOffset + A * initial.childTail) / P at hWord
  rw [hTail, hdiv] at hWord
  change (coupledOrbit A initial K).parentOffset =
    (initial.parentOffset + A * (initial.childTail % P)) / P
  omega

/-- If the high endpoint begins at the true zero carry, the all-Nat controller
tracks the ordinary x4 carry of the child word exactly at every depth. -/
theorem coupledOrbit_childCarry_exact
    (A : Nat) (initial : CoupledState)
    (hC0 : initial.childCarry = 0) :
    ∀ K, (coupledOrbit A initial K).childCarry =
      naturalCarry initial.childTail K := by
  intro K
  induction K with
  | zero =>
      simp [coupledOrbit, naturalCarry, hC0, Nat.mod_one]
  | succ K ih =>
      rw [coupledOrbit]
      change cellNextCarry (coupledOrbit A initial K).childCarry
        ((coupledOrbit A initial K).childTail % 3) = _
      rw [ih, naturalCarry_forward]
      congr 1
      rw [coupledOrbit_childTail_exact A initial K]
      rfl

/-- At every depth the next visible child information digit in the controller
is the actual ternary digit of the original child natural. -/
theorem coupledOrbit_childDigit_exact
    (A : Nat) (initial : CoupledState) :
    ∀ K, (coupledOrbit A initial K).childTail % 3 =
      digit initial.childTail K := by
  intro K
  rw [coupledOrbit_childTail_exact]
  rfl

/-- A finite child natural eventually has zero visible Future, while the
coupled state and its exact invariant continue to exist for every later `K`. -/
theorem coupledOrbit_child_horizon
    (A : Nat) (initial : CoupledState) :
    ∀ K, initial.childTail + 1 ≤ K →
      (coupledOrbit A initial K).childTail = 0 := by
  intro K hK
  rw [coupledOrbit_childTail_exact]
  have hpow : 3^(initial.childTail+1) ≤ 3^K :=
    Nat.pow_le_pow_of_le (by decide : 1 < 3) hK
  exact Nat.div_eq_of_lt
    (lt_of_lt_of_le (self_lt_three_pow_succ initial.childTail) hpow)

/-- Production package for controlled information transport. -/
structure InfiniteCoupledControl
    (A : Nat) (initial : CoupledState) : Prop where
  multiplierPositive : 0 < A
  initialInvariant : CoupledInvariant A initial
  invariantAll : ∀ K, CoupledInvariant A (coupledOrbit A initial K)
  childTailExact : ∀ K,
    (coupledOrbit A initial K).childTail = initial.childTail / 3^K
  parentWordExact : ∀ K,
    (coupledOrbit A initial K).parentWord A =
      initial.parentWord A / 3^K

/-- Every valid initial shared state generates a genuine all-Nat controlled
orbit.  No finite cutoff is used to construct the orbit. -/
theorem infinite_coupled_control
    (A : Nat) (initial : CoupledState)
    (hA : 0 < A) (h0 : CoupledInvariant A initial) :
    InfiniteCoupledControl A initial := by
  exact {
    multiplierPositive := hA
    initialInvariant := h0
    invariantAll := coupledOrbit_invariant_all A initial hA h0
    childTailExact := coupledOrbit_childTail_exact A initial
    parentWordExact := coupledOrbit_parentWord_exact A initial
  }

end GSTV2
