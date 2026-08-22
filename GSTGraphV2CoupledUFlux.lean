import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2CoupledUFlux

/-!
# GST Graph V2: coupled U-flux experiment

This file is based directly on the latest `codex/recent-atomic-victory-v2`
monolith.  The graph is Nat-indexed at every observation depth and has no
terminal/last-gate/support-horizon premise.

The two handwritten operators are normalized here as:

* the U/Omega equation: an exact weighted jump/telescope;
* the 2/3/6 equation: horizontal x2 transport and vertical x3 transport share
  one coupled state, so their mixed scale is x6.

The new experiment is a coupled potential.  Parent U-flux minus the horizontal
multiplier times child U-flux is an exact discrete derivative on the graph.
-/

/-- One live node of the coupled GST V2 graph.  `parentOffset` is the
horizontal residue coordinate; `childTail` is the still-live vertical origin
word.  No coordinate is declared terminal. -/
structure State where
  parentSeed : Nat
  parentOffset : Nat
  childCarry : Nat
  childTail : Nat
  deriving Repr

/-- The child ternary information emitted at the current graph node. -/
def childDigit (st : State) : Nat := st.childTail % 3

/-- The parent ternary information emitted by the same coupled node. -/
def parentDigit (A : Nat) (st : State) : Nat :=
  (st.parentOffset + A * childDigit st) % 3

/-- One exact vertical graph edge.  The parent and child x4 carries regenerate
simultaneously while the parent offset and child tail are divided by three. -/
def step (A : Nat) (st : State) : State :=
  {
    parentSeed := gstStepCarryS st.parentSeed (parentDigit A st)
    parentOffset := (st.parentOffset + A * childDigit st) / 3
    childCarry := gstStepCarryS st.childCarry (childDigit st)
    childTail := st.childTail / 3
  }

/-- The unbounded Nat-indexed orbit.  `K` is an observation coordinate, not a
termination index. -/
def orbit (A : Nat) (initial : State) : Nat → State
  | 0 => initial
  | K+1 => step A (orbit A initial K)

/-- Parent handwritten U-jump at one graph node. -/
def parentJump (A : Nat) (st : State) : Int :=
  gstHandwrittenUJumpS st.parentSeed (parentDigit A st)

/-- Child handwritten U-jump at one graph node. -/
def childJump (st : State) : Int :=
  gstHandwrittenUJumpS st.childCarry (childDigit st)

/-- Coupled U-potential.  The coefficient 24 is exactly `4*6`, matching the
handwritten mixed six-world scale. -/
def potential (A : Nat) (st : State) : Int :=
  (gstHandwrittenUChargeS st.parentSeed : Int) -
    (A : Int) * (gstHandwrittenUChargeS st.childCarry : Int) +
    24 * (st.parentOffset : Int)

/-- Pure algebraic core of the coupled flux equation. -/
private theorem coupled_u_flux_algebra
    (A Z r e Z' Up Up' Uc Uc' : Int)
    (h : Z + A*r = e + 3*Z') :
    (3*Up' - Up - 24*e) - A*(3*Uc' - Uc - 24*r) =
      3*(Up' - A*Uc' + 24*Z') - (Up - A*Uc + 24*Z) := by
  nlinarith [h]

/-- **Experimental Equation III — Coupled U-Flux Derivative.**

At every graph edge, with no badness, finiteness, terminal state, or canonical
specialization assumed,

`parent U-jump - A * child U-jump = 3*Phi(next) - Phi(now)`.

The only nontrivial arithmetic input is the exact base-three quotient law for
the parent horizontal residue. -/
theorem coupled_u_flux_step_exact (A : Nat) (st : State) :
    parentJump A st - (A : Int) * childJump st =
      3 * potential A (step A st) - potential A st := by
  let r := childDigit st
  let e := parentDigit A st
  let Z' := (st.parentOffset + A*r) / 3
  have hsplitNat :
      st.parentOffset + A*r = e + 3*Z' := by
    have h := Nat.mod_add_div (st.parentOffset + A*r) 3
    dsimp [e, Z', parentDigit, r, childDigit]
    omega
  have hsplitInt :
      (st.parentOffset : Int) + (A : Int)*(r : Int) =
        (e : Int) + 3*(Z' : Int) := by
    exact_mod_cast hsplitNat
  have halg := coupled_u_flux_algebra
    (A : Int) (st.parentOffset : Int) (r : Int) (e : Int) (Z' : Int)
    (gstHandwrittenUChargeS st.parentSeed : Int)
    (gstHandwrittenUChargeS (gstStepCarryS st.parentSeed e) : Int)
    (gstHandwrittenUChargeS st.childCarry : Int)
    (gstHandwrittenUChargeS (gstStepCarryS st.childCarry r) : Int)
    hsplitInt
  dsimp [parentJump, childJump, potential, step,
    gstHandwrittenUJumpS, e, r, Z', parentDigit, childDigit] at halg ⊢
  exact halg

/-- Weighted all-depth telescope of Experimental Equation III.  This is the
operator-level `Omega` form: every finite observation window is exact and the
live upper state is retained explicitly. -/
theorem coupled_u_flux_telescope_exact
    (A : Nat) (initial : State) (K : Nat) :
    Finset.sum (Finset.range K) (fun j =>
      ((3^j : Nat) : Int) *
        (parentJump A (orbit A initial j) -
          (A : Int) * childJump (orbit A initial j))) =
      ((3^K : Nat) : Int) * potential A (orbit A initial K) -
        potential A initial := by
  induction K with
  | zero => simp [orbit]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep := coupled_u_flux_step_exact A (orbit A initial K)
      rw [orbit]
      rw [hstep]
      push_cast
      rw [Nat.pow_succ]
      push_cast
      ring

/-- Exact mixed exponential identity from the second handwritten page, retained
inside the graph experiment for arbitrary information depth. -/
theorem mixed_world_scale_exact (K : Nat) :
    6^K = 2^K * 3^K := by
  rw [show (6 : Nat) = 2*3 by decide, mul_pow]

#check coupled_u_flux_step_exact
#check coupled_u_flux_telescope_exact
#check mixed_world_scale_exact
#print axioms coupled_u_flux_step_exact
#print axioms coupled_u_flux_telescope_exact
#print axioms mixed_world_scale_exact

end GSTGraphV2CoupledUFlux
