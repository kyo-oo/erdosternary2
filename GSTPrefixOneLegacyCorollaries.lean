import GSTPrefixOneSeedCore

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTPrefixOneLegacyCorollaries

open GSTCanonicalTailStateIso
open GSTPerfectPowerTailNavigation
open GSTPrefixOneOntologicalEscape
open GSTSeedOneShift
open GSTPrefixOneSeedCore

/-- Complete ordinary physical bad trace: no Happy coordinate exists. -/
def CompleteBadTrace (R : Nat) : Prop :=
  ∀ p : Nat, ¬ HappyCell (carry4 R p) (digit3 R p)

/-- Complete seed-one bad trace on a stripped parent tail. -/
def SeedOneBadTrace (X : Nat) : Prop :=
  ∀ j : Nat, ¬ (digit3 X j = 2 ∧
    (seedOneCarry X j = 0 ∨ seedOneCarry X j = 3))

/-- Standalone form of the old child-to-parent prefix-one contract. -/
def GSTPrefixOneNavigationLift : Prop :=
  ∀ s n : Nat,
    1 ≤ s → 1 ≤ n →
    Navigation (canonicalTail (s+1) n) →
    Navigation (canonicalTail s (1 + 3*n))

/-- The old prefix-one Navigation lift is now a direct corollary of POE.
The child witness is intentionally unused because the conclusion is unconditional. -/
theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn _hchild
  exact gst_prefix_one_ontological_escape s n hs hn

/-- Standalone old seed-core contract. -/
def GSTPrefixOneSeedCore : Prop :=
  ∀ s n : Nat,
    1 ≤ s → 1 ≤ n →
    Navigation (canonicalTail (s+1) n) →
    SeedOneWitness
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n)

/-- The old seed core is immediate from the unconditional strengthened seed theorem. -/
theorem gst_prefix_one_seed_core : GSTPrefixOneSeedCore := by
  intro s n hs hn _hchild
  exact gst_prefix_one_seed_one_parent_unconditional s n hs hn

/-- A seed-one parent bad trace is impossible, unconditionally. -/
theorem gst_prefix_one_seed_one_bad_impossible
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ¬ SeedOneBadTrace
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n) := by
  intro hBad
  obtain ⟨j, hGate⟩ := gst_prefix_one_seed_one_parent_unconditional s n hs hn
  exact hBad j hGate

/-- Replacement for the old atomic collision: parent badness already contradicts POE;
the child witness is no longer part of the mechanism. -/
theorem gst_prefix_one_atomic_collision
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (_hchild : Navigation (canonicalTail (s+1) n))
    (hBad : SeedOneBadTrace
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n)) : False := by
  exact (gst_prefix_one_seed_one_bad_impossible s n hs hn) hBad

/-- Replacement for old bad-reflection/information-descent implications.
Since the parent bad premise is itself impossible, any child bad conclusion follows. -/
theorem gst_prefix_one_information_bad_descends
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : SeedOneBadTrace
      (prefixOffset s + 4^(3^s) * canonicalTail (s+1) n)) :
    CompleteBadTrace (canonicalTail (s+1) n) := by
  exact False.elim ((gst_prefix_one_seed_one_bad_impossible s n hs hn) hBad)

/-- Ordinary parent badness is also impossible directly from POE. -/
theorem gst_prefix_one_parent_complete_bad_impossible
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n) :
    ¬ CompleteBadTrace (canonicalTail s (1 + 3*n)) := by
  intro hBad
  obtain ⟨p, hHappy⟩ := gst_prefix_one_ontological_escape s n hs hn
  exact hBad p hHappy

end GSTPrefixOneLegacyCorollaries
