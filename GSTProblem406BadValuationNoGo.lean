import GSTFourPowerDirectResidue
import Mathlib

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Mathbox exact counterexample to the proposed 4L/3 BAD valuation bound

THIS IS NOT A COUNTEREXAMPLE TO THE ORIGINAL FOUR-POWER CONJECTURE.
The original source is exactly 4^K; this synthetic BAD source is
143*2^67. The purpose is to exclude an invalid proposed universal
auxiliary lemma and prevent its use as the final closure of hGate.

All claims below are exact, with every ternary digit certified:
below L=47 by finite kernel evaluation, above it by the power cutoff.
-/

namespace GSTProblem406BadValuationNoGo

open GSTFourPowerDirectResidue

def badCounterexample : Nat := 21103075220323727048704

/-- Literal source has d0=1, fits inside 47 ternary places,
and has binary order 67, strictly ABOVE floor(4*47/3)=62. -/
theorem counterexample_exact_origin_data :
    badCounterexample % 3 = 1 ∧
    badCounterexample < 3^47 ∧
    (2:Nat)^67 ∣ badCounterexample ∧
    (4*47)/3 < 67 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · refine ⟨143, ?_⟩
    norm_num [badCounterexample]
  · decide

/-- Every positive ternary row of R and 4R avoids simultaneous 2,
not just a bounded sample. -/
theorem counterexample_no_common_two_any_row
    (p : Nat) :
    ¬ (digit3 badCounterexample p=2 ∧
       digit3 (4*badCounterexample) p=2) := by
  by_cases hlow : p < 47
  · have hfinite : ∀ q : Fin 47,
        ¬ (digit3 badCounterexample q.val=2 ∧
           digit3 (4*badCounterexample) q.val=2) := by decide
    exact hfinite ⟨p, hlow⟩
  · have hle : 47 ≤ p := by omega
    have hpow : (3:Nat)^47 ≤ 3^p :=
      Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat)) hle
    have hlt : badCounterexample < 3^p :=
      lt_of_lt_of_le counterexample_exact_origin_data.2.1 hpow
    have hz : digit3 badCounterexample p=0 := by
      unfold digit3
      rw [Nat.div_eq_of_lt hlt]
    omega

/-- Refutation of the full all-length 4L/3 dyadic BAD exclusion.
The exact pure-power source K is NOT quantified here. -/
theorem not_universal_bad_four_thirds_bound :
    ¬ (∀ (L R : Nat),
      11 ≤ L → R%3=1 → 0<R → R<3^L →
      (∀ p : Nat, 1 ≤ p →
        ¬ (digit3 R p=2 ∧ digit3 (4*R) p=2)) →
      ¬ ((2:Nat)^((4*L)/3+1) ∣ R)) := by
  intro h
  have hno := h 47 badCounterexample
    (by decide) counterexample_exact_origin_data.1
    (by decide) counterexample_exact_origin_data.2.1
    (by
      intro p hp
      exact counterexample_no_common_two_any_row p)
  apply hno
  have hp : (4*47)/3+1 ≤ 67 := by decide
  exact dvd_trans (pow_dvd_pow 2 hp)
    counterexample_exact_origin_data.2.2.1

#print axioms counterexample_exact_origin_data
#print axioms counterexample_no_common_two_any_row
#print axioms not_universal_bad_four_thirds_bound

end GSTProblem406BadValuationNoGo
