import GSTGraphV2CanonicalRenormalization
import GSTGraphV2InfiniteControllerBridge
import GSTFinalPrefixOneStep6Infinite

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2CanonicalEscape

open GSTCanonicalSevenAxisBridge
open GSTU2DEventTransport
open GSTPerfectPowerTailNavigation
open GSTPrefixOneSeedCore
open GSTGraphV2InfiniteControl
open GSTGraphV2InfiniteControllerBridge
open GSTGraphV2SeededPrefix
open GSTGraphV2CanonicalRenormalization

/-- The canonical child after removing its forced low prefix. -/
def canonicalChildTail (s n : Nat) : Nat :=
  canonicalTail (s+1) n

/-- The exact unconsumed seed-one parent tail. -/
def canonicalParentTail (s n : Nat) : Nat :=
  prefixOffset s + 4^(3^s) * canonicalChildTail s n

/-- Exact low-prefix decomposition at the child boundary. -/
theorem canonical_child_energy_decomposition
    (s n : Nat) :
    4^(3^(s+1) * n) =
      1 + 3^(s+2) * canonicalChildTail s n := by
  simpa [canonicalChildTail, Nat.add_assoc] using
    canonical_tail_decomposition (s+1) n

/-- Exact low-prefix decomposition one canonical horizontal block to the
right.  This is the arithmetic adapter consumed by the all-depth controller. -/
theorem canonical_parent_energy_decomposition
    (s n : Nat) :
    4^(3^s) * 4^(3^(s+1) * n) =
      (1 + 3^(s+1)) + 3^(s+2) * canonicalParentTail s n := by
  have hpow :
      4^(3^s) * 4^(3^(s+1) * n) =
        4^(3^s * (1 + 3*n)) := by
    rw [← Nat.pow_add]
    congr 1
    rw [Nat.pow_succ]
    ring
  have hcanon := canonical_tail_decomposition s (1 + 3*n)
  rw [canonicalTail_one_strip] at hcanon
  rw [hpow, hcanon]
  unfold canonicalParentTail canonicalChildTail
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  ring

private theorem index_le_three_pow (r : Nat) :
    r ≤ 3^r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Nat.pow_succ]
      have hp : 0 < 3^r := by positivity
      omega

/-- A natural number cannot have nonzero ternary digits beyond every cutoff. -/
theorem nat_no_unbounded_ternary_support
    (n : Nat) :
    ¬ (∀ K : Nat,
      ∃ r : Nat, K ≤ r ∧ (n / 3^r) % 3 ≠ 0) := by
  intro h
  obtain ⟨r, hr, hnonzero⟩ := h (n+1)
  have hnr : n < r := by omega
  have hpow : n < 3^r := lt_of_lt_of_le hnr (index_le_three_pow r)
  have hdiv : n / 3^r = 0 := Nat.div_eq_of_lt hpow
  simp [hdiv] at hnonzero

#check canonical_child_energy_decomposition
#check canonical_parent_energy_decomposition
#check nat_no_unbounded_ternary_support
#print axioms canonical_parent_energy_decomposition
#print axioms nat_no_unbounded_ternary_support

end GSTGraphV2CanonicalEscape
