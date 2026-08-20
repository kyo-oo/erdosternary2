import GSTGraphV2InfiniteElevenEquationMasterScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite six-world / finite-origin collision

The canonical origin-modulus theorem in the physical branch says that the
`6^K` origin universe stores `n mod 6^K`.  The infinite BIG1-clear projector
stores the maximal six-world word `6^K-1`.  This standalone module proves the
arithmetic collision once those two coordinates are synchronized.

The strongest useful form below does **not** require synchronization at every
world.  Cofinal synchronization -- one synchronized scale beyond every finite
cutoff -- is already impossible for an ordinary natural origin.
-/

/-- No ordinary natural origin can be the maximal residue in every `6^K`
world simultaneously. -/
theorem gst_natural_origin_not_maximal_in_all_six_worldsS (n : Nat) :
    ¬ (∀ K, n % 6^K = 6^K - 1) := by
  intro hmax
  have hK := hmax (n+1)
  have hp : n + 1 < 6^(n+1) :=
    Nat.lt_pow_self (by decide : 1 < 6)
  have hlt : n < 6^(n+1) := by omega
  rw [Nat.mod_eq_of_lt hlt] at hK
  omega

/-- Exact synchronization interface between a canonical finite origin and one
infinite microscopic V2 path. -/
def GSTInfiniteSixWorldOriginSynchronizationS
    (n : Nat) (a d : Nat → Nat) : Prop :=
  ∀ K, gstBig1ProjectedPathCodeS a d K = n % 6^K

/-- A nonzero all-depth `I != BIG1` path cannot synchronize with all finite
`6^K` origin universes of any ordinary natural. -/
theorem gst_no_finite_origin_synchronizes_with_infinite_big1_clear_worldS
    (n : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (hsync : GSTInfiniteSixWorldOriginSynchronizationS n a d) : False := by
  apply gst_natural_origin_not_maximal_in_all_six_worldsS n
  intro K
  have hcode := gst_big1_clear_infinite_all_six_prefixes_maximalS
    a d hpath h0 K
  have hsyncK := hsync K
  rw [hcode] at hsyncK
  exact hsyncK.symm

/-- Equivalent exclusion form: for every finite origin there is some six-world
scale at which its canonical origin residue cannot equal the infinite maximal
projector code. -/
theorem gst_finite_origin_escapes_infinite_big1_clear_codeS
    (n : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∃ K, n % 6^K ≠ gstBig1ProjectedPathCodeS a d K := by
  by_contra hnone
  have hall : ∀ K, n % 6^K = gstBig1ProjectedPathCodeS a d K := by
    intro K
    by_contra hne
    exact hnone ⟨K, hne⟩
  exact gst_no_finite_origin_synchronizes_with_infinite_big1_clear_worldS
    n a d hpath h0 (fun K => (hall K).symm)

/-- Cofinal synchronization: beyond every requested scale there is a later
`6^K` world where the infinite projector code and the canonical finite-origin
residue are identified.  This is strictly weaker than all-scale
synchronization and is the natural interface for an Omega re-realisation
argument. -/
def GSTCofinalSixWorldOriginSynchronizationS
    (n : Nat) (a d : Nat → Nat) : Prop :=
  ∀ M, ∃ K, M ≤ K ∧
    gstBig1ProjectedPathCodeS a d K = n % 6^K

/-- Even cofinally many synchronized maximal worlds are impossible for a
finite natural origin.  In particular a future physical-realisation theorem
only needs to manufacture synchronized worlds at arbitrarily high selected
scales, not at every scale. -/
theorem gst_no_finite_origin_cofinally_synchronizes_big1_clear_worldS
    (n : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (hcofinal : GSTCofinalSixWorldOriginSynchronizationS n a d) : False := by
  obtain ⟨K, hKlarge, hsyncK⟩ := hcofinal (n+1)
  have hcode := gst_big1_clear_infinite_all_six_prefixes_maximalS
    a d hpath h0 K
  have hKlt : K < 6^K := Nat.lt_pow_self (by decide : 1 < 6)
  have hnlt : n < 6^K := by omega
  have hmod : n % 6^K = n := Nat.mod_eq_of_lt hnlt
  rw [hcode, hmod] at hsyncK
  have hpowpos : 0 < 6^K := Nat.pow_pos (by decide)
  omega

/-- Negated cofinal form: every finite origin admits a cutoff beyond which no
selected maximal six-world code can keep agreeing with its canonical residue
at all later scales. -/
theorem gst_finite_origin_has_six_world_desynchronization_cutoffS
    (n : Nat) (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∃ M, ∀ K, M ≤ K →
      gstBig1ProjectedPathCodeS a d K ≠ n % 6^K := by
  refine ⟨n+1, ?_⟩
  intro K hKlarge hEq
  apply gst_no_finite_origin_cofinally_synchronizes_big1_clear_worldS
    n a d hpath h0
  intro M
  let L := max M K
  refine ⟨L, le_max_left _ _, ?_⟩
  by_cases hLK : L = K
  · subst L
    exact hEq
  · have hKL : K < L := by
      have hKleL : K ≤ L := le_max_right _ _
      omega
    have hcodeL := gst_big1_clear_infinite_all_six_prefixes_maximalS
      a d hpath h0 L
    have hLpow : L < 6^L := Nat.lt_pow_self (by decide : 1 < 6)
    have hnL : n < 6^L := by
      have hnK : n < K := by omega
      omega
    have hmodL : n % 6^L = n := Nat.mod_eq_of_lt hnL
    rw [hcodeL, hmodL]
    have hpos : 0 < 6^L := Nat.pow_pos (by decide)
    omega

end GSTInfiniteV2
