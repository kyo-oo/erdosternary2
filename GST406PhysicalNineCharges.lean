import GST406CenteredUConservation
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST 406 — complete nine-class physical U budget

At base-three slice b=3 the exact coupled source observables
depend only on 4^K modulo 27. Since 4^9 = 1 (mod 27),
the centered global U budget has nine EXACT source classes,
uniformly for EVERY K. These are arithmetic theorems about
literal 4^K, with no hGate assumption and no finite K horizon.

The sign of the nine charges is NOT uniform. Consequently the
original local sign argument cannot close by a blanket
positive/negative boundary claim.
-/

namespace GST406PhysicalNineCharges

open GSTCanonicalSevenAxisBridge
open GST2DMixedEmergence
open GSTGraphV2CoupledUFlux
open GSTGraphV2InfiniteControl
open GSTGraphV2UnifiedPowerRectangle
open GST406CenteredUConservation

private theorem pow4_mod_twentyseven_shift_nine
    (K : Nat) :
    (4:Nat)^(K+9)%27=4^K%27 := by
  have h9 : (4:Nat)^9%27=1 := by decide
  calc
    (4:Nat)^(K+9)%27 = (4^K*4^9)%27 := by rw [pow_add]
    _ = ((4^K%27)*(4^9%27))%27 := Nat.mul_mod _ _ _
    _ = 4^K%27 := by rw [h9]; simp

private theorem graph_carry_source_shift_nine
    (K t : Nat) :
    (graph (4^(K+9)) t 3).seven.carry =
      (graph (4^K) t 3).seven.carry := by
  have h9 := pow4_mod_twentyseven_shift_nine K
  have hmod :
      (4^t*4^(K+9))%27=(4^t*4^K)%27 := by
    calc
      (4^t*4^(K+9))%27 =
          ((4^t%27)*(4^(K+9)%27))%27 := Nat.mul_mod _ _ _
      _ = ((4^t%27)*(4^K%27))%27 := by rw [h9]
      _ = (4^t*4^K)%27 := (Nat.mul_mod _ _ _).symm
  change 4*((4^t*4^(K+9))%27)/27 =
      4*((4^t*4^K)%27)/27
  rw [hmod]

private theorem width_three_word_period_nine (K : Nat) :
    carryWord (4^(K+9)) 3 0 3 = carryWord (4^K) 3 0 3 := by
  have h0 := graph_carry_source_shift_nine K 0
  have h1 := graph_carry_source_shift_nine K 1
  have h2 := graph_carry_source_shift_nine K 2
  simp [carryWord, h0, h1, h2]

/-- Exact all-K period-nine source boundary for the full
centered U conservation law. -/
theorem centered_origin_period_nine (K : Nat) :
    centeredPotential (K+9) 3 = centeredPotential K 3 := by
  have h0 := graph_carry_source_shift_nine K 0
  have h3 := graph_carry_source_shift_nine K 3
  have hw := width_three_word_period_nine K
  change
    (gstUChargeExact (graph (4^(K+9)) 3 3).seven.carry -
      (((4^3 : Nat) : Int)) *
        gstUChargeExact (graph (4^(K+9)) 0 3).seven.carry +
      24*(carryWord (4^(K+9)) 3 0 3 : Int)) + 315 =
    (gstUChargeExact (graph (4^K) 3 3).seven.carry -
      (((4^3 : Nat) : Int)) *
        gstUChargeExact (graph (4^K) 0 3).seven.carry +
      24*(carryWord (4^K) 3 0 3 : Int)) + 315
  rw [h0,h3,hw]

/-- The complete fixed nine class table, independently validated by
Wolfram exact power/modular arithmetic, source K from 0 through 8.
Negativity is genuine at classes 3 and 8. -/
def sourceChargeNine (r : Nat) : Int :=
  if r=0 then 58
  else if r=1 then 226
  else if r=2 then 264
  else if r=3 then -78
  else if r=4 then 96
  else if r=5 then 402
  else if r=6 then 440
  else if r=7 then 224
  else if r=8 then -246
  else 0

private theorem source_charge_nine_base
    (r : Nat) (hr : r < 9) :
    centeredPotential r 3 = sourceChargeNine r := by
  interval_cases r <;> decide

private theorem centered_origin_period_multiple
    (r n : Nat) :
    centeredPotential (r+9*n) 3 = centeredPotential r 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hidx : r+9*(n+1)=(r+9*n)+9 := by omega
      rw [hidx, centered_origin_period_nine, ih]

/-- Universal exact source-origin charge classification by K mod 9,
without restricting K to a computed range. -/
theorem centered_origin_all_k_nine_class (K : Nat) :
    centeredPotential K 3=sourceChargeNine (K%9) := by
  have hre : K=K%9 + 9*(K/9) := by
    have h := Nat.mod_add_div K 9
    omega
  calc
    centeredPotential K 3 =
        centeredPotential (K%9+9*(K/9)) 3 :=
      congrArg (fun n : Nat => centeredPotential n 3) hre
    _ = centeredPotential (K%9) 3 :=
      centered_origin_period_multiple (K%9) (K/9)
    _ = sourceChargeNine (K%9) :=
      source_charge_nine_base (K%9) (Nat.mod_lt K (by decide))

/-- Exact full physical K-word U budget is one of nine finite
integers, uniformly in every exponent K and all terminal H.
It is an identity, not a proof that a BAD trajectory is impossible. -/
theorem all_k_full_word_budget_nine_class
    (K H : Nat) (hH : 3 ≤ H)
    (htail : (4:Nat)^(K+4) ≤ H) :
    Finset.sum (Finset.range (H-3)) (fun j =>
      (((3^j:Nat):Int)) *
        (physicalUDifference K (3+j)+630)) =
      -sourceChargeNine (K%9) := by
  rw [physical_full_word_compensated_budget K 3 H hH htail,
      centered_origin_all_k_nine_class]

#print axioms centered_origin_period_nine
#print axioms source_charge_nine_base
#print axioms centered_origin_all_k_nine_class
#print axioms all_k_full_word_budget_nine_class

end GST406PhysicalNineCharges
