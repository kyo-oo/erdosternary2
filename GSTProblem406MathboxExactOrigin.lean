import GSTProblem406PhysicalCutGateEquivalence
import GSTProblem406BinaryOriginSmallCases

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# GST Problem 406: exact binary origin at the physically certified ternary end

This file closes the exact arithmetic step in the Deep Research report. It
does NOT claim to discharge hGate: the missing mathematical theorem is the
nonexistence of a BAD carry trace for these exact binary source powers.

The endpoint's binary exponent is NOT merely bounded below; for K>=13
it equals either 2K or 2K-1, according to K modulo 3. This is proved
using only Presburger identities and exponent laws, no oracle/certificate
or new hypothesis. The final equivalence uses the *same* source 4^K
and exact cutoff as the earlier Lean-verified theorem.
-/

namespace GSTProblem406MathboxExactOrigin

open GSTProblem406BinaryOriginExponentScale
open GSTProblem406PhysicalCutGateEquivalence
open GSTFourPowerDirectExistence
open GSTFourPowerDirectResidue

/-- The binary source threshold in the report, defined at the exact
K-dependent physical ternary cutoff. -/
def threshold (K : Nat) : Nat :=
  (3 * physicalShortCut K)/2+1

/-- The physical integer singled out by the research report:
NO generic surrogate, no free high-divisibility multiplier. -/
def exactBinaryOrigin (K : Nat) : Nat :=
  if K % 3 = 0 then 2^(threshold K+1) else 2^(threshold K)

/-- Completely resolve the exact threshold by K mod 3. -/
theorem exact_binary_threshold_exponents
    (K : Nat) (hK : 13 ≤ K) :
    (K % 3 = 0 ∧ 2*K = threshold K+1) ∨
    (K % 3 ≠ 0 ∧ 2*K = threshold K) := by
  by_cases h0 : K%3=0
  · left
    refine ⟨h0, ?_⟩
    unfold threshold physicalShortCut
    omega
  · right
    refine ⟨h0, ?_⟩
    unfold threshold physicalShortCut
    omega

/-- The exact original source really is exactly the report's
two-case binary origin, rather than an arbitrary multiple of it. -/
theorem exact_binary_origin_eq_four_pow
    (K : Nat) (hK : 13 ≤ K) :
    exactBinaryOrigin K = 4^K := by
  have hp : (4:Nat)^K = 2^(2*K) := by
    rw [show (4:Nat) = 2^2 by decide, pow_mul]
  rcases exact_binary_threshold_exponents K hK with
    ⟨hzero, hexp⟩ | ⟨hnonzero, hexp⟩
  · simp only [exactBinaryOrigin, hzero, if_pos, hp, hexp]
  · simp only [exactBinaryOrigin, if_neg hnonzero, hp, hexp]

/-- A precise biconditional for the ACTUAL residual universal gate:
every K>=13 is a counterexample exactly when its exact binary origin
avoids all common-two rows before the proven physical terminal cut.

This is an honest equivalent restatement, not the missing exclusion. -/
theorem commonTwo_iff_exact_binary_origin_hit
    (K : Nat) (hK : 13 ≤ K) :
    CommonTwo K ↔
      ∃ p : Nat, 1 ≤ p ∧ p < physicalShortCut K ∧
        digit3 (exactBinaryOrigin K) p = 2 ∧
        digit3 (4 * exactBinaryOrigin K) p = 2 := by
  rw [commonTwo_iff_sharp_physical_cut K hK]
  have hp : (4:Nat)^(K+1) = 4*(4^K) := by
    rw [pow_succ]
    ring
  simp only [exact_binary_origin_eq_four_pow K hK, hp]

#print axioms exact_binary_threshold_exponents
#print axioms exact_binary_origin_eq_four_pow
#print axioms commonTwo_iff_exact_binary_origin_hit

end GSTProblem406MathboxExactOrigin
