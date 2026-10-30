import GSTGraphV2UnifiedVerticalTelescope
import GSTProblem406TightPhysicalCut
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Problem 406 — physical terminal U-potential at the exact pure-power cut

The old proposed 3-step collision stalled at a local linarith step.
The missing information is a GLOBAL boundary transfer between the
positive child phase window and an all-BAD parent phase window.

This new module establishes the actually justified terminal
condition of the exact GST U-telescope for EVERY genuine 4^K, K≥13.

In particular, at a physical height p with 256 E <3^p, all three
horizontal interior carries, plus the right/left boundary carries,
and the child tail are exactly ZERO. Therefore the U potential is
5 - 64*5 = -315. This is a mathematical boundary equality, NOT
the desired all-K CommonTwo gate and not a sign contradiction.
-/

namespace GSTProblem406TerminalUBoundary

open GSTCanonicalSevenAxisBridge
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope
open GSTGraphV2CoupledUFlux
open GSTProblem406TightPhysicalCut

private theorem carry_zero_of_four_mul_lt
    (R p : Nat) (h : 4*R < 3^p) :
    carry4 R p = 0 := by
  unfold carry4
  have hm : R % 3^p ≤ R := Nat.mod_le _ _
  have hlt : 4*(R % 3^p) < 3^p := by omega
  rw [Nat.div_eq_of_lt hlt]

/-- Universal exact terminal GST U potential, for a FINITE input E.
This is true for all E, but we then specialize E=4^K with
a kernel-proved source-specific physical height. -/
theorem exact_terminal_u_potential
    (E p : Nat) (h : 256*E < 3^p) :
    potentialWith gstUChargeExact (4^3)
      (unifiedState E 3 p).core = -315 := by
  have h0 : carry4 E p = 0 :=
    carry_zero_of_four_mul_lt E p (by omega)
  have h1 : carry4 (4*E) p = 0 :=
    carry_zero_of_four_mul_lt (4*E) p (by omega)
  have h2 : carry4 (16*E) p = 0 :=
    carry_zero_of_four_mul_lt (16*E) p (by omega)
  have h3 : carry4 (64*E) p = 0 :=
    carry_zero_of_four_mul_lt (64*E) p (by omega)
  have htail : E / 3^p = 0 := Nat.div_eq_of_lt (by omega)
  have hword : carryWord E p 0 3 = 0 := by
    norm_num [carryWord, graph, cell, vertex, h0, h1, h2]
  change
    gstUChargeExact (carry4 (4^3*E) p) -
      (((4^3 : Nat) : Int)) * gstUChargeExact (carry4 E p) +
        24 * ((carryWord E p 0 3 : Nat) : Int) = -315
  norm_num [gstUChargeExact, h0, h3, hword]

/-- The pure source 4^K has a completely explicit *finite* terminal
height, using the already verified 24/19 physical cutoff. -/
def terminalHeight (K : Nat) : Nat :=
  tighterPhysicalCut (K+3) + 2

theorem source_256_below_terminal_height
    (K : Nat) (hK : 13 ≤ K) :
    256 * 4^K < 3^(terminalHeight K) := by
  have hphys :=
    physical_source_lt_tighter_cut (K+3) (by omega)
  have hpower : (256:Nat)*4^K = 4 * 4^(K+3) := by
    calc
      256*4^K = 4^4*4^K := by norm_num
      _ = 4^(4+K) := (pow_add 4 4 K).symm
      _ = 4^((K+3)+1) := by
        congr 1
        omega
      _ = 4*4^(K+3) := by rw [pow_succ]; ring
  calc
    256*4^K = 4*4^(K+3) := hpower
    _ < 4*3^(tighterPhysicalCut (K+3)) :=
      Nat.mul_lt_mul_of_pos_left hphys (by decide)
    _ ≤ 9*3^(tighterPhysicalCut (K+3)) := by omega
    _ = 3^(terminalHeight K) := by
      unfold terminalHeight
      rw [pow_add]
      norm_num

/-- Pure-power terminal coefficient is EXACTLY -315, for EVERY K≥13.
This is axiom-free boundary information not used by the existing
failing line 176 of the original universal navigation proof. -/
theorem pure_source_terminal_u_potential
    (K : Nat) (hK : 13 ≤ K) :
    potentialWith gstUChargeExact (4^3)
      (unifiedState (4^K) 3 (terminalHeight K)).core = -315 := by
  exact exact_terminal_u_potential (4^K) (terminalHeight K)
    (source_256_below_terminal_height K hK)

/-- The telescope from row 3 to the exact terminal row has no
unidentified terminal potential. It supplies a true global
balance, but it DOES NOT alone force a BAD parent impossible:
both the child and parent jumps can compensate each other. -/
theorem pure_source_terminal_u_telescope
    (K : Nat) (hK : 13 ≤ K) :
    let H := terminalHeight K-3
    Finset.sum (Finset.range H) (fun j =>
      (((3^j : Nat) : Int)) *
        (gstUJumpExact
            (graph (4^K) 3 (3+j)).seven.carry
            (graph (4^K) 3 (3+j)).seven.digit -
          (64 : Int) * gstUJumpExact
            (graph (4^K) 0 (3+j)).seven.carry
            (graph (4^K) 0 (3+j)).seven.digit)) =
      -315 * (((3^H : Nat) : Int)) -
        potentialWith gstUChargeExact 64
          (unifiedState (4^K) 3 3).core := by
  dsimp only
  have hheight : 3+(terminalHeight K-3)=terminalHeight K := by
    unfold terminalHeight tighterPhysicalCut
    omega
  have h := unified_equationIII_vertical_telescope
    (4^K) 3 3 (terminalHeight K-3)
  rw [hheight, pure_source_terminal_u_potential K hK] at h
  norm_num at h ⊢
  nlinarith [h]

#print axioms exact_terminal_u_potential
#print axioms source_256_below_terminal_height
#print axioms pure_source_terminal_u_potential
#print axioms pure_source_terminal_u_telescope

end GSTProblem406TerminalUBoundary
