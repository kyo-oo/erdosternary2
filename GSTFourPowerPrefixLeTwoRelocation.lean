import GSTFourPowerExactRowRelocation

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerPrefixLeTwoRelocation

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerExponentTritObstruction
open GSTFourPowerExactRowRelocation

/-- A single parametric constructor covering the first three low-prefix
sectors at once.  At every scale `p ≥ 3`, if the low exponent prefix of the
next exponent is at most two and the current exponent trit is two, then the
physical relocated row is exactly `p+1`.

This is still the fresh direct exponent-prefix route: no navigation,
transport, or existential witness substitution is used. -/
theorem prefix_le_two_two_trit_forces_relocated_happy_at_exact_row
    (K p : Nat) (hp : 3 ≤ p)
    (hpref : exponentPrefix (K+1) p ≤ 2)
    (htrit : exponentTrit (K+1) p = 2) :
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) (p+1))
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) (p+1)) := by
  have hcases :
      exponentPrefix (K+1) p = 0 ∨
      exponentPrefix (K+1) p = 1 ∨
      exponentPrefix (K+1) p = 2 := by
    omega
  rcases hcases with h0 | h1 | h2
  · apply leading_two_small_prefix_forces_relocated_happy_at_exact_row K p htrit
    simpa [h0] using four_lt_three_pow_succ p (by omega)
  · apply leading_two_small_prefix_forces_relocated_happy_at_exact_row K p htrit
    simpa [h1] using sixteen_lt_three_pow_succ p (by omega)
  · apply leading_two_small_prefix_forces_relocated_happy_at_exact_row K p htrit
    simpa [h2] using sixty_four_lt_three_pow_succ p hp

/-- Witness-bearing Task-3 form of the bounded-prefix constructor.  The row is
not re-selected: the theorem returns the concrete physical witness `q=p+1`. -/
theorem prefix_le_two_two_trit_constructs_exact_relocated_row
    (K p : Nat) (hp : 3 ≤ p)
    (hpref : exponentPrefix (K+1) p ≤ 2)
    (htrit : exponentTrit (K+1) p = 2) :
    ∃ q : Nat, q = p+1 ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  refine ⟨p+1, rfl, by omega, ?_⟩
  exact prefix_le_two_two_trit_forces_relocated_happy_at_exact_row
    K p hp hpref htrit

#check prefix_le_two_two_trit_forces_relocated_happy_at_exact_row
#check prefix_le_two_two_trit_constructs_exact_relocated_row
#print axioms prefix_le_two_two_trit_forces_relocated_happy_at_exact_row
#print axioms prefix_le_two_two_trit_constructs_exact_relocated_row

end GSTFourPowerPrefixLeTwoRelocation
