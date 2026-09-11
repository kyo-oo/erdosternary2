import GSTFourPowerDirectHappyBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerExactRowRelocation

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerDirectAdditionCarry
open GSTFourPowerExponentTritObstruction
open GSTFourPowerDirectHappyBridge

/-- If two consecutive four-powers have digit two at a specified row, that
same row is physically Happy on the source power.  This is the row-preserving
form of the direct CommonTwo bridge: no existential witness is re-selected. -/
theorem commonTwo_exact_row_to_physical_happy
    (K q : Nat)
    (hs : digit3 (4^K) q = 2)
    (ht : digit3 (4^(K+1)) q = 2) :
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^K) q)
      (GSTCanonicalTailStateIso.digit3 (4^K) q) := by
  unfold GSTCanonicalTailStateIso.HappyCell
  constructor
  · simpa [GSTCanonicalTailStateIso.digit3,
      GSTFourPowerDirectResidue.digit3] using hs
  · have ht4 : digit3 (4 * (4^K)) q = 2 := by
      simpa [pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using ht
    have hformula := digit3_four_mul (4^K) q
    have hs' : digit3 (4^K) q = 2 := hs
    rw [hs', ht4] at hformula
    have hcarry : directCarry4 (4^K) q = 0 ∨ directCarry4 (4^K) q = 3 := by
      have hlt := directCarry4_lt_four (4^K) q
      omega
    simpa [GSTCanonicalTailStateIso.carry4, directCarry4] using hcarry

/-- Exact-row form of the parametric killing-trit constructor.  The arithmetic
normal form determines the relocated physical row itself: it is `q = p+1`.
No navigation, packet transport, or existential witness substitution occurs. -/
theorem prefix_killing_trit_forces_relocated_happy_at_exact_row
    (K p : Nat)
    (heq :
      digit3 (4^(exponentPrefix (K+1) p)) (p+1) =
      digit3 (4^((exponentPrefix (K+1) p)+1)) (p+1))
    (hkill :
      exponentTrit (K+1) p =
        2 - digit3 (4^(exponentPrefix (K+1) p)) (p+1)) :
    GSTCanonicalTailStateIso.HappyCell
      (GSTCanonicalTailStateIso.carry4 (4^(K+1)) (p+1))
      (GSTCanonicalTailStateIso.digit3 (4^(K+1)) (p+1)) := by
  have hrow :=
    (row_common_two_iff_prefix_killing_trit (K+1) p).2 ⟨heq, hkill⟩
  exact commonTwo_exact_row_to_physical_happy (K+1) (p+1) hrow.1 hrow.2

/-- Witness-bearing Task-3-shaped version.  Under the exact prefix/trit
condition, the produced relocated witness is definitionally the row `p+1`. -/
theorem prefix_killing_trit_constructs_exact_relocated_row
    (K p : Nat)
    (heq :
      digit3 (4^(exponentPrefix (K+1) p)) (p+1) =
      digit3 (4^((exponentPrefix (K+1) p)+1)) (p+1))
    (hkill :
      exponentTrit (K+1) p =
        2 - digit3 (4^(exponentPrefix (K+1) p)) (p+1)) :
    ∃ q : Nat, q = p+1 ∧ 1 ≤ q ∧
      GSTCanonicalTailStateIso.HappyCell
        (GSTCanonicalTailStateIso.carry4 (4^(K+1)) q)
        (GSTCanonicalTailStateIso.digit3 (4^(K+1)) q) := by
  refine ⟨p+1, rfl, by omega, ?_⟩
  exact prefix_killing_trit_forces_relocated_happy_at_exact_row K p heq hkill

#check commonTwo_exact_row_to_physical_happy
#check prefix_killing_trit_forces_relocated_happy_at_exact_row
#check prefix_killing_trit_constructs_exact_relocated_row
#print axioms commonTwo_exact_row_to_physical_happy
#print axioms prefix_killing_trit_forces_relocated_happy_at_exact_row
#print axioms prefix_killing_trit_constructs_exact_relocated_row

end GSTFourPowerExactRowRelocation
