import GSTFourPowerDirectExistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# Exact Archimedean finite termination window for original hGate

Every original physical 4^K is finite, and its common-two
witness must lie strictly below 2(K+1)+1 in the ternary row index.
No 3-adic limit, infinite suffix assumption or custom existence
axiom is needed. This is the exact bounded decidable reformulation
of the original universal predicate, NOT a proof of its truth.

The research problem becomes proving the bounded existential
certificate for ALL natural K>=5 with K!=7.
-/

namespace GSTProblem406FiniteNaturalTermination

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence

/-- Effective original ternary row bound for one natural exponent. -/
def physicalEndRow (K : Nat) : Nat := 2*(K+1)+1

/-- The original perfect power is strictly below its certified
last ternary row's place value. -/
theorem physical_source_below_end_cut (K : Nat) :
    4^K < 3^(physicalEndRow K) := by
  have hmono : 4^K ≤ 4^(K+1) := by
    rw [pow_succ]
    omega
  have hbase : 4^(K+1) ≤ 9^(K+1) := by gcongr <;> norm_num
  have hnine : 9^(K+1) = 3^(2*(K+1)) := by
    calc
      9^(K+1) = (3^2)^(K+1) := by norm_num
      _ = 3^(2*(K+1)) := by rw [pow_mul]
  have hpos : 0 < 3^(2*(K+1)) := by positivity
  calc
    4^K ≤ 4^(K+1) := hmono
    _ ≤ 9^(K+1) := hbase
    _ = 3^(2*(K+1)) := hnine
    _ < 3^(physicalEndRow K) := by
      simp only [physicalEndRow]
      rw [pow_succ]
      omega

/-- Beyond this line the physical source has only zero ternary trits.
The result depends on the finite actual integer 4^K, not a 3-adic
extension or generic affine input. -/
theorem original_physical_source_digit_vanishes_above_end
    (K p : Nat) (hp : physicalEndRow K ≤ p) :
    digit3 (4^K) p = 0 := by
  have hpow : 3^(physicalEndRow K) ≤ 3^p := by
    gcongr
    omega
  have hlt : 4^K < 3^p :=
    lt_of_lt_of_le (physical_source_below_end_cut K) hpow
  unfold digit3
  rw [Nat.div_eq_of_lt hlt]

/-- Original unlimited CommonTwo is EXACTLY a finite physical
witness check with an explicit K-dependent Archimedean cutoff. -/
theorem commonTwo_iff_physical_finite_search (K : Nat) :
    CommonTwo K ↔
      ∃ p : Nat, 1 ≤ p ∧ p < physicalEndRow K ∧
        digit3 (4^K) p = 2 ∧
        digit3 (4^(K+1)) p = 2 := by
  constructor
  · rintro ⟨p,hp,hs,hn⟩
    by_cases hBound : p < physicalEndRow K
    · exact ⟨p,hp,hBound,hs,hn⟩
    · have hzero :=
        original_physical_source_digit_vanishes_above_end K p (by omega)
      omega
  · rintro ⟨p,hp,_,hs,hn⟩
    exact ⟨p,hp,hs,hn⟩

/-- Failure of CommonTwo is equivalently a finite universal
arithmetic assertion on all rows before the true end cut. -/
theorem noCommonTwo_iff_every_row_below_end_is_bad (K : Nat) :
    ¬ CommonTwo K ↔
      ∀ p : Nat, 1 ≤ p → p < physicalEndRow K →
        ¬ (digit3 (4^K) p = 2 ∧
           digit3 (4^(K+1)) p = 2) := by
  rw [commonTwo_iff_physical_finite_search]
  push_neg
  rfl

#print axioms physical_source_below_end_cut
#print axioms original_physical_source_digit_vanishes_above_end
#print axioms commonTwo_iff_physical_finite_search
#print axioms noCommonTwo_iff_every_row_below_end_is_bad

end GSTProblem406FiniteNaturalTermination
