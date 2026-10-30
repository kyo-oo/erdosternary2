import GSTGraphV2UnifiedVerticalTelescope
import GSTGraphV2PerfectPowerBlockProbe
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST 406 — exact physical terminal U-flux, all powers of four

This investigates the last failed tactic inside
`GSTInfiniteFourPowerNavigation.power_three_step_collision`.
The U equation is an equality, not a monotonic positivity law.
For every genuine E=4^K, all graph digits and carries in the
width-three rectangle eventually vanish. The full physical
coupled U potential stabilizes to 5-64*5 = -315, but its
vertical defect stabilizes to -630, NOT to zero.

This proves the precise endpoint of the original exact
Equation III and makes the attempted local-to-global sign
transfer testable; it does not assume, replace or prove the
universal CommonTwo gate.
-/

namespace GST406PhysicalUTerminal

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GSTGraphV2UnifiedVerticalTelescope

/-- Uniform elementary exponent domination, with no probabilistic input:
3^n grows strictly faster than the integer n itself. -/
private theorem nat_lt_three_pow (n : Nat) :
    n < (3:Nat)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have hpos : 0 < (3:Nat)^n := by positivity
    omega

/-- Genuine 4^K is the SOURCE, and each of its first four
horizontal columns vanishes beyond a concrete uniform terminal cut.
The extremely conservative cutoff is used ONLY to establish a
fully uniform kernel theorem; no sharp numerical estimate is needed. -/
theorem physical_terminal_graph_cell
    (K t p : Nat) (ht : t ≤ 3)
    (hp : (4:Nat)^(K+4) ≤ p) :
    (graph (4^K) t p).seven.carry = 0 ∧
    (graph (4^K) t p).seven.digit = 0 := by
  have hpow :
      (4:Nat)^(K+t+1) ≤ 4^(K+4) :=
    Nat.pow_le_pow_of_le (by decide : 1 < (4:Nat)) (by omega)
  have hshape :
      4*(4^t*4^K) = (4:Nat)^(K+t+1) := by
    rw [show K+t+1 = K+(t+1) by omega, pow_add, pow_succ]
    ring
  have hcap : (4:Nat)^(K+4) < 3^p := by
    have hstart := nat_lt_three_pow ((4:Nat)^(K+4))
    have hraise : (3:Nat)^(4^(K+4)) ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hp
    omega
  have hbound : 4*(4^t*4^K) < 3^p := by
    rw [hshape]
    omega
  have hsource : 4^t*4^K < 3^p := by omega
  constructor
  · change (4*((4^t*4^K)%3^p))/3^p = 0
    rw [Nat.mod_eq_of_lt hsource, Nat.div_eq_of_lt hbound]
  · change ((4^t*4^K)/3^p)%3 = 0
    rw [Nat.div_eq_of_lt hsource]
    decide

/-- At all sufficiently high physical rows, the original retained
width-three carry word is EXACTLY ZERO. -/
theorem physical_terminal_carry_word
    (K p : Nat) (hp : (4:Nat)^(K+4) ≤ p) :
    carryWord (4^K) p 0 3 = 0 := by
  have hc0 := (physical_terminal_graph_cell K 0 p (by decide) hp).1
  have hc1 := (physical_terminal_graph_cell K 1 p (by decide) hp).1
  have hc2 := (physical_terminal_graph_cell K 2 p (by decide) hp).1
  simp [carryWord, hc0, hc1, hc2]

/-- Nonzero baseline! The true coupled U potential is permanently -315
in the physical high-zero tail. Replacing it by 0 silently changes the
source mathematics. -/
theorem physical_terminal_u_potential
    (K p : Nat) (hp : (4:Nat)^(K+4) ≤ p) :
    potentialWith gstUChargeExact (4^3)
        (unifiedState (4^K) 3 p).core = -315 := by
  have hc0 := (physical_terminal_graph_cell K 0 p (by decide) hp).1
  have hc3 := (physical_terminal_graph_cell K 3 p (by decide) hp).1
  have hw := physical_terminal_carry_word K p hp
  change gstUChargeExact (graph (4^K) 3 p).seven.carry -
      (((4^3 : Nat) : Int)) *
        gstUChargeExact (graph (4^K) 0 p).seven.carry +
      24*(carryWord (4^K) p 0 3 : Int) = -315
  rw [hc0, hc3, hw]
  norm_num [gstUChargeExact]

/-- Although ALL high rows are BAD, Equation III's physical vertical
defect is STRICTLY NEGATIVE there. This is the global sign
compensation missing from a local-positive-slope argument. -/
theorem physical_terminal_u_defect
    (K p : Nat) (hp : (4:Nat)^(K+4) ≤ p) :
    gstUJumpExact
        (graph (4^K) 3 p).seven.carry
        (graph (4^K) 3 p).seven.digit -
      ((4^3 : Nat) : Int) *
        gstUJumpExact
          (graph (4^K) 0 p).seven.carry
          (graph (4^K) 0 p).seven.digit = -630 := by
  obtain ⟨hc0,hd0⟩ :=
    physical_terminal_graph_cell K 0 p (by decide) hp
  obtain ⟨hc3,hd3⟩ :=
    physical_terminal_graph_cell K 3 p (by decide) hp
  rw [hc0,hd0,hc3,hd3]
  norm_num [gstUJumpExact, jumpWith, gstUChargeExact, gstStepCarryExact]

/-- The exact Equation-III derivative matches the nonzero terminal
potential, and its sign reverses the local positive derivative. -/
theorem physical_terminal_equationIII_negative
    (K p : Nat) (hp : (4:Nat)^(K+4) ≤ p) :
    3*potentialWith gstUChargeExact (4^3)
        (unifiedState (4^K) 3 (p+1)).core -
      potentialWith gstUChargeExact (4^3)
        (unifiedState (4^K) 3 p).core = -630 := by
  have hpnext : (4:Nat)^(K+4) ≤ p+1 := by omega
  rw [physical_terminal_u_potential K (p+1) hpnext,
      physical_terminal_u_potential K p hp]
  norm_num

#print axioms physical_terminal_graph_cell
#print axioms physical_terminal_carry_word
#print axioms physical_terminal_u_potential
#print axioms physical_terminal_u_defect
#print axioms physical_terminal_equationIII_negative

end GST406PhysicalUTerminal
