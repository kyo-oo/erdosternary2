import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CoupledUFlux

/-!
# GST Graph V2 — red-seam-independent coupled U-flux core

This module deliberately does **not** import `ErdosTernary2`: the latest Codex
monolith has the one known RED obligation.  The equations below are therefore
kernel-testable independently and can later be instantiated with the monolith's
exact `gstStepCarryS`, `gstHandwrittenUChargeS`, and canonical phase state.

Nothing terminates here.  `K : Nat` is always an observation coordinate.
-/

/-- A live node of the coupled graph. -/
structure State where
  parentSeed : Nat
  parentOffset : Nat
  childCarry : Nat
  childTail : Nat
  deriving Repr

/-- Current child information trit. -/
def childDigit (st : State) : Nat := st.childTail % 3

/-- Current parent information trit represented by horizontal multiplier `A`. -/
def parentDigit (A : Nat) (st : State) : Nat :=
  (st.parentOffset + A * childDigit st) % 3

/-- One graph edge for an arbitrary carry-regeneration law.  This abstraction
lets the algebraic theorem be proved before importing the RED monolith. -/
def stepWith (nextCarry : Nat → Nat → Nat) (A : Nat) (st : State) : State :=
  {
    parentSeed := nextCarry st.parentSeed (parentDigit A st)
    parentOffset := (st.parentOffset + A * childDigit st) / 3
    childCarry := nextCarry st.childCarry (childDigit st)
    childTail := st.childTail / 3
  }

/-- U-jump generated from an arbitrary charge chart and carry law. -/
def jumpWith
    (charge : Nat → Int) (nextCarry : Nat → Nat → Nat)
    (C d : Nat) : Int :=
  3 * charge (nextCarry C d) - charge C - 24 * (d : Int)

def parentJumpWith
    (charge : Nat → Int) (nextCarry : Nat → Nat → Nat)
    (A : Nat) (st : State) : Int :=
  jumpWith charge nextCarry st.parentSeed (parentDigit A st)

def childJumpWith
    (charge : Nat → Int) (nextCarry : Nat → Nat → Nat)
    (st : State) : Int :=
  jumpWith charge nextCarry st.childCarry (childDigit st)

/-- Coupled graph potential.  The `24 = 4*6` coefficient is the mixed
2/3/6-space information charge appearing in the handwritten U operator. -/
def potentialWith (charge : Nat → Int) (A : Nat) (st : State) : Int :=
  charge st.parentSeed - (A : Int) * charge st.childCarry +
    24 * (st.parentOffset : Int)

/-- Pure algebraic kernel. -/
private theorem coupled_u_flux_algebra
    (A Z r e Z' Up Up' Uc Uc' : Int)
    (h : Z + A*r = e + 3*Z') :
    (3*Up' - Up - 24*e) - A*(3*Uc' - Uc - 24*r) =
      3*(Up' - A*Uc' + 24*Z') - (Up - A*Uc + 24*Z) := by
  nlinarith [h]

/-- **Experimental Equation III — Coupled U-Flux Derivative.**

For *every* charge chart, carry law, multiplier, and live graph node,

`parentJump - A*childJump = 3*Phi(next) - Phi(now)`.

The result is all-depth and representation-independent: no badness assumption,
last gate, support horizon, finite search, or terminal NULL state occurs. -/
theorem coupled_u_flux_step_exact
    (charge : Nat → Int) (nextCarry : Nat → Nat → Nat)
    (A : Nat) (st : State) :
    parentJumpWith charge nextCarry A st -
        (A : Int) * childJumpWith charge nextCarry st =
      3 * potentialWith charge A (stepWith nextCarry A st) -
        potentialWith charge A st := by
  let r := childDigit st
  let e := parentDigit A st
  let Z' := (st.parentOffset + A*r) / 3
  have hsplitNat : st.parentOffset + A*r = e + 3*Z' := by
    have h := Nat.mod_add_div (st.parentOffset + A*r) 3
    dsimp [e, Z', parentDigit, r, childDigit]
    omega
  have hsplitInt :
      (st.parentOffset : Int) + (A : Int)*(r : Int) =
        (e : Int) + 3*(Z' : Int) := by
    exact_mod_cast hsplitNat
  have halg := coupled_u_flux_algebra
    (A : Int) (st.parentOffset : Int) (r : Int) (e : Int) (Z' : Int)
    (charge st.parentSeed)
    (charge (nextCarry st.parentSeed e))
    (charge st.childCarry)
    (charge (nextCarry st.childCarry r))
    hsplitInt
  dsimp [parentJumpWith, childJumpWith, jumpWith, potentialWith,
    stepWith, e, r, Z', parentDigit, childDigit] at halg ⊢
  exact halg

/-- Nat-indexed orbit of the same coupled graph. -/
def orbitWith
    (nextCarry : Nat → Nat → Nat) (A : Nat) (initial : State) :
    Nat → State
  | 0 => initial
  | K+1 => stepWith nextCarry A (orbitWith nextCarry A initial K)

/-- Weighted Ω-form of Equation III.  Every finite observation window is exact
and the upper state remains live on the right-hand side. -/
theorem coupled_u_flux_telescope_exact
    (charge : Nat → Int) (nextCarry : Nat → Nat → Nat)
    (A : Nat) (initial : State) (K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      ((3^j : Nat) : Int) *
        (parentJumpWith charge nextCarry A
            (orbitWith nextCarry A initial j) -
          (A : Int) * childJumpWith charge nextCarry
            (orbitWith nextCarry A initial j))) =
      ((3^K : Nat) : Int) *
          potentialWith charge A (orbitWith nextCarry A initial K) -
        potentialWith charge A initial := by
  induction K with
  | zero => simp [orbitWith]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := coupled_u_flux_step_exact charge nextCarry A
        (orbitWith nextCarry A initial K)
      rw [orbitWith]
      rw [hstep]
      push_cast
      rw [Nat.pow_succ]
      push_cast
      ring

/-! ## Exact standalone GST specialization

These three definitions are literal copies of the arithmetic formulas in the
latest Codex monolith.  They are named locally so this green kernel does not
need to import the RED file.
-/

def gstStepCarryExact (C d : Nat) : Nat := (C + 4*d) / 3

def gstUChargeExact (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

def gstUJumpExact (C d : Nat) : Int :=
  jumpWith gstUChargeExact gstStepCarryExact C d

/-- Exact twelve-state U-jump table used by the production GST coordinates. -/
theorem gst_u_jump_exact_table :
    gstUJumpExact 0 0 = 10 ∧
    gstUJumpExact 0 1 = 16 ∧
    gstUJumpExact 0 2 = -8 ∧
    gstUJumpExact 1 0 = 0 ∧
    gstUJumpExact 1 1 = 6 ∧
    gstUJumpExact 1 2 = 0 ∧
    gstUJumpExact 2 0 = 0 ∧
    gstUJumpExact 2 1 = 6 ∧
    gstUJumpExact 2 2 = 0 ∧
    gstUJumpExact 3 0 = 24 ∧
    gstUJumpExact 3 1 = 0 ∧
    gstUJumpExact 3 2 = -6 := by
  decide

/-- Equation III specialized to the exact GST charge/carry chart. -/
theorem gst_coupled_u_flux_step_exact (A : Nat) (st : State) :
    parentJumpWith gstUChargeExact gstStepCarryExact A st -
        (A : Int) * childJumpWith gstUChargeExact gstStepCarryExact st =
      3 * potentialWith gstUChargeExact A
          (stepWith gstStepCarryExact A st) -
        potentialWith gstUChargeExact A st :=
  coupled_u_flux_step_exact gstUChargeExact gstStepCarryExact A st

/-- Equation II — exact mixed exponential coupling from the second handwritten
page. -/
theorem mixed_world_scale_exact (K : Nat) :
    6^K = 2^K * 3^K := by
  rw [show (6 : Nat) = 2*3 by decide, mul_pow]

#check coupled_u_flux_step_exact
#check coupled_u_flux_telescope_exact
#check gst_coupled_u_flux_step_exact
#check mixed_world_scale_exact
#print axioms coupled_u_flux_step_exact
#print axioms coupled_u_flux_telescope_exact
#print axioms gst_coupled_u_flux_step_exact
#print axioms mixed_world_scale_exact

end GSTGraphV2CoupledUFlux
