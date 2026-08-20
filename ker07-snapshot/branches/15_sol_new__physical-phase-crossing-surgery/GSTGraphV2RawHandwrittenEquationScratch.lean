import GSTGraphV2InfiniteElevenEquationMasterScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Raw handwritten equation — full typed GST V2 laboratory

Literal transcription from the 2026-08-20 page:

  Π_{t→∞}^{n≠0} { ∫_{∞}^{-∞} (lim_{j→∞} e^x) }
    2^j ∪ 3^j ∪ 6^j - f_m ∪ Σ_{S≠0}^{S≠3^x} S n^x

Important: the handwritten symbol is `S`, not the numeral 5.

We do not silently turn the union symbols into multiplication.  The three
radix worlds are represented as literal finite-set unions.  The unknown
`f_m` glyph is kept parameterized as a removable finite sector `fm`, so no
mathematical meaning is invented for it.

The handwritten Π was previously specified as the constructor of all spaces,
so its GST interpretation is the actual all-Nat seven-axis orbit.  The
reverse ∞→-∞ bracket is represented by the exact Omega digit-transfer
reconstruction already proved in the infinite controller, rather than by an
unjustified classical improper integral.
-/

/-- Binary, ternary and mixed six-worlds as literal state spaces. -/
def gstRawThreeWorldUnionS (j : Nat) : Finset Nat :=
  (Finset.range (2^j) ∪ Finset.range (3^j)) ∪ Finset.range (6^j)

/-- The S-sector written with the boundary exclusions S != 0 and S != 3^x.
`range (3^x)` already excludes the upper endpoint; erasing zero enforces the
lower exclusion literally. -/
def gstRawSpaceIndexS (x : Nat) : Finset Nat :=
  (Finset.range (3^x)).erase 0

/-- The handwritten weighted S-sum. -/
def gstRawSpaceWeightedSumS (n x : Nat) : Nat :=
  Finset.sum (gstRawSpaceIndexS x) (fun S => S * n^x)

/-- `- f_m` is typed as removal of an as-yet uninterpreted sector. -/
def gstRawWholeSpaceSupportS (j x : Nat) (fm : Finset Nat) : Finset Nat :=
  (gstRawThreeWorldUnionS j \ fm) ∪ gstRawSpaceIndexS x

/-- Exact binary/ternary cardinal join underlying the mixed 6-world. -/
theorem gst_raw_three_world_cardinal_joinS (j : Nat) :
    2^j * 3^j = 6^j := by
  have h := Nat.mul_pow 2 3 j
  norm_num at h
  exact h.symm

/-- Literal union test: the mixed six-world contains both component worlds,
so the three handwritten unions collapse exactly to the six-world support. -/
theorem gst_raw_three_world_union_eq_sixS (j : Nat) :
    gstRawThreeWorldUnionS j = Finset.range (6^j) := by
  have h26 : 2^j ≤ 6^j := by gcongr
  have h36 : 3^j ≤ 6^j := by gcongr
  ext r
  simp only [gstRawThreeWorldUnionS, Finset.mem_union, Finset.mem_range]
  omega

/-- Exact semantics of the two handwritten S-boundary conditions. -/
theorem gst_raw_space_index_memS (S x : Nat) :
    S ∈ gstRawSpaceIndexS x ↔ S ≠ 0 ∧ S < 3^x := by
  simp [gstRawSpaceIndexS, and_comm]

/-- Therefore every selected S is simultaneously away from both displayed
boundaries. -/
theorem gst_raw_space_index_avoids_boundariesS
    (S x : Nat) (hS : S ∈ gstRawSpaceIndexS x) :
    S ≠ 0 ∧ S ≠ 3^x := by
  have h := (gst_raw_space_index_memS S x).1 hS
  exact ⟨h.1, by omega⟩

/-- Once the literal unions are evaluated, the whole support part of the page
is exactly the mixed six-world with `fm` removed, union the interior S-sector. -/
theorem gst_raw_whole_support_normal_formS
    (j x : Nat) (fm : Finset Nat) :
    gstRawWholeSpaceSupportS j x fm =
      (Finset.range (6^j) \ fm) ∪ gstRawSpaceIndexS x := by
  rw [gstRawWholeSpaceSupportS, gst_raw_three_world_union_eq_sixS]

/-- The displayed limit is constant in j if `e^x` is read literally as the
real exponential.  This isolates the classical part without assigning a
spurious finite value to the reversed infinite integral. -/
theorem gst_raw_exp_limit_literalS (x : ℝ) :
    Filter.Tendsto (fun _ : Nat => Real.exp x) Filter.atTop (𝓝 (Real.exp x)) := by
  exact tendsto_const_nhds

/-- Full typed GST interpretation of the handwritten expression.  It keeps
all seven graph axes, the all-depth constructor, the exact past/future reverse
transfer, the literal three-world union, the unknown f_m removal, and the
weighted S-sector in one object. -/
structure GSTRawHandwrittenEquationV2S
    (R N n x j : Nat) (fm : Finset Nat) : Prop where
  allSpaceConstructor : ∀ t,
    (gstGraphV2InfiniteOrbitS R N (t+1)).carry =
      gstStepCarryS
        (gstGraphV2InfiniteOrbitS R N t).carry
        (gstGraphV2InfiniteOrbitS R N t).digit
  reverseInfiniteTransfer : ∀ t T K,
    Finset.sum (Finset.range K) (fun i => gstOmegaNaturalTransferS t T i) =
      3^(t+1) * (T % 3^K)
  literalExpLimit : ∀ y : ℝ,
    Filter.Tendsto (fun _ : Nat => Real.exp y) Filter.atTop (𝓝 (Real.exp y))
  threeWorldCardinality : 2^j * 3^j = 6^j
  threeWorldUnion : gstRawThreeWorldUnionS j = Finset.range (6^j)
  sBoundaryLaw : ∀ S, S ∈ gstRawSpaceIndexS x → S ≠ 0 ∧ S ≠ 3^x
  weightedSSum : gstRawSpaceWeightedSumS n x =
    Finset.sum (gstRawSpaceIndexS x) (fun S => S * n^x)
  wholeSupport : gstRawWholeSpaceSupportS j x fm =
    (Finset.range (6^j) \ fm) ∪ gstRawSpaceIndexS x

/-- The complete readable equation is internally coherent under the typed GST
V2 interpretation above, at every natural depth; no finite cutoff is used. -/
theorem gst_raw_handwritten_equation_v2_masterS
    (R N n x j : Nat) (fm : Finset Nat) :
    GSTRawHandwrittenEquationV2S R N n x j fm := by
  refine {
    allSpaceConstructor := ?_
    reverseInfiniteTransfer := ?_
    literalExpLimit := ?_
    threeWorldCardinality := gst_raw_three_world_cardinal_joinS j
    threeWorldUnion := gst_raw_three_world_union_eq_sixS j
    sBoundaryLaw := ?_
    weightedSSum := rfl
    wholeSupport := gst_raw_whole_support_normal_formS j x fm }
  · intro t
    exact gst_graph_v2_infinite_orbit_stepS R N t
  · intro t T K
    exact gst_omega_natural_transfer_prefixS t T K
  · intro y
    exact gst_raw_exp_limit_literalS y
  · intro S hS
    exact gst_raw_space_index_avoids_boundariesS S x hS

#check gst_raw_three_world_cardinal_joinS
#check gst_raw_three_world_union_eq_sixS
#check gst_raw_space_index_memS
#check gst_raw_whole_support_normal_formS
#check gst_raw_handwritten_equation_v2_masterS
#print axioms gst_raw_handwritten_equation_v2_masterS

end GSTInfiniteV2
