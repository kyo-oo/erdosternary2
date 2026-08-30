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


private theorem canonical_cut_gt_four
    (s : Nat) (hs : 1 ≤ s) :
    4 < 3^(s+2) := by
  have h27 : 27 ≤ 3^(s+2) := by
    rw [show (27 : Nat) = 3^3 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  omega

private theorem canonical_right_prefix_lt_cut
    (s : Nat) (hs : 1 ≤ s) :
    1 + 3^(s+1) < 3^(s+2) := by
  rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
  have hp : 0 < 3^(s+1) := by positivity
  omega

private theorem canonical_right_prefix_seed_one
    (s : Nat) (hs : 1 ≤ s) :
    (4 * (1 + 3^(s+1))) / 3^(s+2) = 1 := by
  have h9 : 9 ≤ 3^(s+1) := by
    rw [show (9 : Nat) = 3^2 by decide]
    exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have hden : 0 < 3^(s+2) := by positivity
  have hlo : 3^(s+2) ≤ 4 * (1 + 3^(s+1)) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hhi : 4 * (1 + 3^(s+1)) < 2 * 3^(s+2) := by
    rw [show s+2 = (s+1)+1 by omega, Nat.pow_succ]
    omega
  have hlo' : 1 ≤ (4 * (1 + 3^(s+1))) / 3^(s+2) := by
    exact (Nat.le_div_iff_mul_le hden).2 (by simpa using hlo)
  have hhi' : (4 * (1 + 3^(s+1))) / 3^(s+2) < 2 := by
    exact (Nat.div_lt_iff_lt_mul hden).2 (by simpa using hhi)
  omega

/-- The physical canonical left boundary is exactly the lossless seed-zero
child state. -/
theorem canonical_left_seed_adapter
    (s n q : Nat) (hs : 1 ≤ s) :
    HappyCell
        (graph (4^(3^(s+1) * n)) 0 (s+2+q)).seven.carry
        (graph (4^(3^(s+1) * n)) 0 (s+2+q)).seven.digit ↔
      SeedHappy 0 0 (canonicalChildTail s n) q := by
  have hE :
      4^0 * 4^(3^(s+1) * n) =
        1 + 3^(s+2) * canonicalChildTail s n := by
    simpa using canonical_child_energy_decomposition s n
  have hP : 1 < 3^(s+2) := by
    exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
  have h := graph_prefix_slice_happy_iff
    (4^(3^(s+1) * n)) 0 (s+2) 1 (canonicalChildTail s n) q hE hP
  have hseed : (4 * 1) / 3^(s+2) = 0 :=
    Nat.div_eq_of_lt (canonical_cut_gt_four s hs)
  rw [hseed] at h
  rw [seedHappy_zero_iff]
  simpa [HappyCell, GSTGraphV2InfiniteControl.seededCarry,
    GSTCanonicalSevenAxisBridge.carry4,
    GSTCanonicalSevenAxisBridge.digit3] using h

/-- The physical canonical right boundary is exactly the lossless seed-one
parent state; the complete low prefix is retained. -/
theorem canonical_right_seed_adapter
    (s n q : Nat) (hs : 1 ≤ s) :
    HappyCell
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+q)).seven.carry
        (graph (4^(3^(s+1) * n)) (3^s) (s+2+q)).seven.digit ↔
      SeedHappy 1 1 (canonicalParentTail s n) q := by
  have hE :
      4^(3^s) * 4^(3^(s+1) * n) =
        (1 + 3^(s+1)) + 3^(s+2) * canonicalParentTail s n :=
    canonical_parent_energy_decomposition s n
  have h := graph_prefix_slice_happy_iff
    (4^(3^(s+1) * n)) (3^s) (s+2)
    (1 + 3^(s+1)) (canonicalParentTail s n) q hE
    (canonical_right_prefix_lt_cut s hs)
  have hseed := canonical_right_prefix_seed_one s hs
  rw [seedHappy_one_iff]
  simpa [HappyCell, hseed] using h


/-- The canonical child begins the coupled controller with the true zero
carry, derived from the exact low prefix rather than assumed. -/
theorem canonical_base_carry_zero
    (s n : Nat) (hs : 1 ≤ s) :
    (graph (4^(3^(s+1) * n)) 0 (s+2)).seven.carry = 0 := by
  have hE :
      4^0 * 4^(3^(s+1) * n) =
        1 + 3^(s+2) * canonicalChildTail s n := by
    simpa using canonical_child_energy_decomposition s n
  have hP : 1 < 3^(s+2) := by
    exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
  have hslice := graph_prefix_slice_exact
    (4^(3^(s+1) * n)) 0 (s+2) 1 (canonicalChildTail s n) 0 hE hP
  have hseed : (4 * 1) / 3^(s+2) = 0 :=
    Nat.div_eq_of_lt (canonical_cut_gt_four s hs)
  rw [hseed] at hslice
  simpa [GSTGraphV2InfiniteControl.seededCarry, Nat.mod_one] using hslice.2

/-- Existing all-depth bad control plus the exact canonical adapters produces
the live latent gate packet.  This is the certified controller input to the
remaining renormalized-escape step. -/
theorem canonical_latent_gate_packet
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    GSTV2.LatentGateTransfer
      (4^(3^s))
      (graphCoupledState
        (4^(3^(s+1) * n)) (3^s) (s+2))
      q := by
  apply graph_child_happy_latent_transfer
  · exact canonical_base_carry_zero s n hs
  · intro j hGraph
    exact hRightBad j ((canonical_right_seed_adapter s n j hs).mp hGraph)
  · exact (canonical_left_seed_adapter s n q hs).mpr hChild


/-- The live controller packet has an exact arithmetic consequence: the child
canonical tail retains a nonzero residue through the row immediately after
the supplied Happy gate. -/
theorem canonical_child_residue_packet_nonzero
    (s n q : Nat) (hs : 1 ≤ s)
    (hChild : SeedHappy 0 0 (canonicalChildTail s n) q)
    (hRightBad : ∀ j,
      ¬ SeedHappy 1 1 (canonicalParentTail s n) j) :
    canonicalChildTail s n % 3^(q+1) ≠ 0 := by
  let E : Nat := 4^(3^(s+1) * n)
  let N : Nat := 3^s
  let b : Nat := s+2
  let st := graphCoupledState E N b
  have hRightGraph : ∀ j,
      ¬ HappyCell
        (graph E N (b+j)).seven.carry
        (graph E N (b+j)).seven.digit := by
    intro j hGraph
    apply hRightBad j
    apply (canonical_right_seed_adapter s n j hs).mp
    simpa [E, N, b, Nat.add_assoc] using hGraph
  have hControl : GSTV2.InfiniteBadCoupledControl (4^N) st := by
    dsimp [st]
    apply graph_infinite_bad_control
    · simpa [E, b] using canonical_base_carry_zero s n hs
    · exact hRightGraph
  have hLatent := canonical_latent_gate_packet s n q hs hChild hRightBad
  have hTail :
      E / 3^b = canonicalChildTail s n := by
    have hden : 0 < 3^b := by positivity
    have hsmall : 1 < 3^b := by
      dsimp [b]
      exact lt_trans (by decide : 1 < 4) (canonical_cut_gt_four s hs)
    rw [show E = 1 + 3^b * canonicalChildTail s n by
      simpa [E, b] using canonical_child_energy_decomposition s n]
    rw [Nat.add_mul_div_left _ _ hden]
    rw [Nat.div_eq_of_lt hsmall, Nat.zero_add]
  have hExact := hControl.childCarryExact (q+1)
  have hNonOrbit :
      (GSTV2.coupledOrbit (4^N) st (q+1)).childCarry ≠ 0 := by
    simpa [E, N, b, st] using hLatent.nextCarryNonzero
  have hNaturalState :
      GSTV2.naturalCarry st.childTail (q+1) ≠ 0 := by
    rw [← hExact]
    exact hNonOrbit
  have hNatural :
      GSTV2.naturalCarry (canonicalChildTail s n) (q+1) ≠ 0 := by
    simpa [st, graphCoupledState, hTail] using hNaturalState
  intro hzero
  apply hNatural
  simp [GSTV2.naturalCarry, hzero]

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
#check canonical_left_seed_adapter
#check canonical_right_seed_adapter
#check canonical_base_carry_zero
#check canonical_latent_gate_packet
#check canonical_child_residue_packet_nonzero
#check canonical_parent_energy_decomposition
#check nat_no_unbounded_ternary_support
#print axioms canonical_parent_energy_decomposition
#print axioms nat_no_unbounded_ternary_support

end GSTGraphV2CanonicalEscape
