import GSTGraphV2CanonicalSignedPrefixBridge
import GSTInfiniteCoupledLedger

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalInfiniteCycle

open GSTV2
open GSTGraphV2PerfectPowerBlock
open GSTGraphV2CanonicalEscape

/-- The literal all-depth controller attached to the canonical perfect-power
block.  No terminal height is selected. -/
def canonicalController (s n : Nat) : CoupledState :=
  graphCoupledState
    (canonicalEnergy s n)
    (canonicalWidth s)
    (s + 2)

/-- Iterating for `a+b` rows is exactly iteration for `a` rows followed by
iteration for `b` rows. -/
theorem coupledOrbit_add_exact
    (A : Nat) (initial : CoupledState) (a b : Nat) :
    coupledOrbit A initial (a + b) =
      coupledOrbit A (coupledOrbit A initial a) b := by
  induction b with
  | zero => simp [coupledOrbit]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega]
      rw [coupledOrbit, ih, coupledOrbit]

/-- A repeated complete live controller state repeats at every further turn of
the same cycle.  The theorem retains all five coordinates; it does not project
the controller to a carry/digit label and it does not assume termination. -/
theorem coupledOrbit_cycle_all_turns
    (A : Nat) (initial : CoupledState) (a L : Nat)
    (hcycle :
      coupledOrbit A initial a =
        coupledOrbit A initial (a + L)) :
    ∀ m : Nat,
      coupledOrbit A initial (a + m * L) =
        coupledOrbit A initial a := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        coupledOrbit A initial (a + (m + 1) * L) =
            coupledOrbit A initial ((a + m * L) + L) := by
              congr 2
              omega
        _ = coupledOrbit A (coupledOrbit A initial (a + m * L)) L :=
              coupledOrbit_add_exact A initial (a + m * L) L
        _ = coupledOrbit A (coupledOrbit A initial a) L := by rw [ih]
        _ = coupledOrbit A initial (a + L) :=
              (coupledOrbit_add_exact A initial a L).symm
        _ = coupledOrbit A initial a := hcycle.symm

/-- Canonical specialization of the exact infinite-cycle theorem. -/
theorem canonical_controller_cycle_all_turns
    (s n a L : Nat)
    (hcycle :
      coupledOrbit (4^(canonicalWidth s)) (canonicalController s n) a =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + L)) :
    ∀ m : Nat,
      coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + m * L) =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) a :=
  coupledOrbit_cycle_all_turns
    (4^(canonicalWidth s)) (canonicalController s n) a L hcycle

/-- The exact Past/Future ledger remains available at every turn of a canonical
cycle.  This is the lossless packet required by recurrence-based surgery. -/
theorem canonical_cycle_ledger_packet
    (s n a L : Nat)
    (hcycle :
      coupledOrbit (4^(canonicalWidth s)) (canonicalController s n) a =
        coupledOrbit (4^(canonicalWidth s))
          (canonicalController s n) (a + L)) :
    ∀ m : Nat,
      let initial := canonicalController s n
      initial.parentPast (4^(canonicalWidth s)) (a + m * L) +
          3^(a + m * L) *
            (coupledOrbit (4^(canonicalWidth s)) initial
              (a + m * L)).childResidue =
        initial.childResidue +
          4^(canonicalWidth s) *
            initial.childPast (a + m * L) := by
  intro m
  dsimp only
  exact (infinite_coupled_ledger
    (4^(canonicalWidth s)) (canonicalController s n)
    (by positivity)
    (by
      dsimp [canonicalController]
      exact graphCoupledState_invariant
        (canonicalEnergy s n) (canonicalWidth s) (s + 2))).pastSynchronized
          (a + m * L)

#check coupledOrbit_add_exact
#check coupledOrbit_cycle_all_turns
#check canonical_controller_cycle_all_turns
#check canonical_cycle_ledger_packet
#print axioms coupledOrbit_cycle_all_turns
#print axioms canonical_cycle_ledger_packet

end GSTGraphV2CanonicalInfiniteCycle
