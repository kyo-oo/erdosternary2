import ErdosTernary2
import GSTInfiniteBadTransport

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open GSTV2

/-- Horizontal multiplier of the canonical prefix-one information wave. -/
def gpt56PrefixOneA (s : Nat) : Nat := 4^(3^s)

/-- Canonical initial two-endpoint state.  The high endpoint starts at the true
zero child carry; the low endpoint is exactly the seed-one parent affine word. -/
def gpt56PrefixOneInitialState (s n : Nat) : GSTV2.CoupledState where
  parentSeed := 1
  parentOffset := c s / 3
  childResidue := 1 + 4 * (c s / 3)
  childCarry := 0
  childTail := gstNavigationConstant (s+1) n

/-- The finite high residue really lies below the full horizontal multiplier. -/
theorem gpt56_prefix_one_initial_residue_lt
    (s : Nat) (hs : 1 ≤ s) :
    1 + 4 * (c s / 3) < gpt56PrefixOneA s := by
  have hcmod : c s % 3 = 1 := c_mod3 s hs
  have hcne : c s ≠ 0 := by
    intro h0
    rw [h0] at hcmod
    norm_num at hcmod
  have hcpos : 0 < c s := Nat.pos_of_ne_zero hcne
  have hcdiv : c s / 3 ≤ c s := Nat.div_le_self _ _
  have h4 : 4 * (c s / 3) ≤ 4 * c s :=
    Nat.mul_le_mul_left 4 hcdiv
  have h49 : 4 * c s < 9 * c s := by omega
  have hpow : 9 ≤ 3^(s+1) := by
    have h : 3^2 ≤ 3^(s+1) :=
      Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h ⊢
    exact h
  have h9A : 9 * c s ≤ 3^(s+1) * c s :=
    Nat.mul_le_mul_right (c s) hpow
  have hLTE := lte_identity s hs
  unfold gpt56PrefixOneA
  rw [hLTE]
  omega

/-- The canonical prefix-one state satisfies the exact shared-information
invariant before any child information is consumed. -/
theorem gpt56_prefix_one_initial_invariant
    (s n : Nat) (hs : 1 ≤ s) :
    GSTV2.CoupledInvariant (gpt56PrefixOneA s)
      (gpt56PrefixOneInitialState s n) := by
  constructor
  · simp [gpt56PrefixOneInitialState]
  · simpa [gpt56PrefixOneInitialState] using
      gpt56_prefix_one_initial_residue_lt s hs

/-- Exact parent Ω badness is the production V2 seed-one bad language on the
same affine information word. -/
theorem gpt56_prefix_one_bad_to_v2_seeded
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.SeededBadTrace 1
      ((gpt56PrefixOneInitialState s n).parentWord (gpt56PrefixOneA s)) := by
  have hold := (gst_omega_infiniteBadTrace_iff_seededAffine s 1 n).1 hBad
  have hseed : (4 * (c s % 3^1)) / 3^1 = 1 := by
    rw [Nat.pow_one, c_mod3 s hs]
    decide
  rw [hseed] at hold
  simpa [GSTV2.SeededBadTrace, GSTV2.Happy, GSTV2.affineCarry,
    GSTV2.digit, GSTV2.CoupledState.parentWord,
    gpt56PrefixOneInitialState, gpt56PrefixOneA,
    GSTSeededAffineBadTrace, GSTBadPair, gstAffineMulCarry, gstDigit] using hold

/-- The canonical prefix-one bad assumption therefore generates one exact
all-Nat coupled controller.  Parent badness, child realization, shared-state
conservation, and the support horizon are now coordinates of the same object. -/
theorem gpt56_prefix_one_infinite_bad_control
    (s n : Nat) (hs : 1 ≤ s)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTV2.InfiniteBadCoupledControl
      (gpt56PrefixOneA s) (gpt56PrefixOneInitialState s n) := by
  apply GSTV2.infinite_bad_coupled_control
  · unfold gpt56PrefixOneA
    exact Nat.pow_pos (by decide)
  · exact gpt56_prefix_one_initial_invariant s n hs
  · rfl
  · exact gpt56_prefix_one_bad_to_v2_seeded s n hs hBad

#print axioms gpt56_prefix_one_initial_invariant
#print axioms gpt56_prefix_one_bad_to_v2_seeded
#print axioms gpt56_prefix_one_infinite_bad_control
