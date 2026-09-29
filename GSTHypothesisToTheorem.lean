import ErdosTernary2
import GSTFinalResidualConnector
import GSTFinalPrefixOneStep6Boundary
import GSTStep6CollisionKernel
import GSTU2DSharpCrossingBlock
import GSTGraphV2HandwrittenOmegaUBlock
import GSTGraphV2InfiniteControl
import GST2DMixedEmergence

/-!
# The Hypothesis-to-Theorem Conversion and the k=1 Collision-Core Wire

This file is the interconnection the campaign was missing.  Three proven
fragments that never met are wired here into one socket map, and the war's
original hypothesis — the `FourPowerCreationMaster` statement that the base
commit `de11dc2` carried quarantined inside a comment block — is converted
from a hated axiom-shaped object into a named `Prop` that feeds a theorem.

## The socket map (all inputs interchangeable, all routes certified)

Every route the campaign ever built — the climb route, the two-wave route,
the residual-Ω route, the mirror-bridge route — snaps onto ONE socket: the
creation master `∀ K ≥ 5, K ≠ 7 → CreationCertificate (4^K)`.  This file
proves, from CI-green parts only:

* **THE CONVERSION.**  `erdos_ternary_2_universal_of_hypothesis`: the
  hypothesis, stated as one explicit `Prop` binder, yields the full Erdős
  ternary-2 theorem `∀ n ≥ 9, noTernaryTwo (2^n) = false` through the
  two-wave machinery (`gst_four_power_ontological_navigation_of_master`
  accepts ANY master; the climb was never the mathematical content, only
  one of its suppliers).  The k = 7 exclusion in the hypothesis is exactly
  covered by the kernel-checked base `modular_check_base` (a ≤ 500).

* **THE k=1 COLLISION-CORE WIRE.**  `gst_omega_termination_s1_of_sign_closure`:
  the production connector (`GSTFinalResidualConnector`, green), the
  eq.(37) right-edge sign seam (`GSTFinalPrefixOneStep6Boundary`, green)
  and the sharp crossing positive side (`GSTU2DSharpCrossingBlock`, green)
  compose — given ONE named core, `GSTStep6SignClosure` — into the k=1
  Ω-termination that the reverted revival attempted.  The core is the
  eq.(21) content at canonical k=1 strength: the right-edge crossing sign
  closes the weighted prefix.  It is stated, not assumed as an axiom; it
  is the ONE remaining named link on the residual route.

* **THE INTERCONNECTION.**  `gst_omega_termination_s1_of_hypothesis`: the
  hypothesis closes the SAME k=1 Ω-termination through the atomic seam
  (`gst_prefix_one_navigation_lift_of_master_inline` builds the parent
  Navigation witness from the master; the monolith's atomic Ω-bad theorem
  forbids it).  Two sockets — the hypothesis and the sign-closure core —
  one termination.  The lift chain then runs the monolith's residual
  induction: hypothesis → prefix-one lift → residual lift → universal
  canonical Navigation.

The hypothesis is no longer an axiom to be hated: it is a named premise,
and the implication from it to the conjecture is a machine-checked
theorem.  What remains of the war is one named object per route: the
climb, or the sign-closure core.  Everything else is wired.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl
open GSTU2DExactCrossingCharge
open GSTGraphV2HandwrittenOmegaUBlock

namespace GSTHypothesisToTheorem

/-! ## Section 0 — the hypothesis, named -/

/-- THE WAR'S ORIGINAL HYPOTHESIS, NAMED.  Every `4^K` (K ≥ 5, K ≠ 7)
carries a creation certificate: a ternary digit-two position shared
through the x4/base-3 carry propagation with the next power.  At the base
commit this statement sat quarantined inside a comment block; every route
built since consumes exactly this object. -/
def erdos_ternary_2_creation_hypothesis : Prop :=
  GSTFourPowerOntologicalAdapter.FourPowerCreationMaster

/-- The hypothesis IS the creation master socket input, verbatim. -/
theorem creation_master_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis) :
    GSTFourPowerOntologicalAdapter.FourPowerCreationMaster := h

/-! ## Section 1 — the conversion: hypothesis → theorem -/

/-- The two consecutive power waves overlap at a Happy Gate — run directly
on the hypothesis socket.  Body identical to the monolith's green
`gst_power_two_wave_large`, with the master supplied by the hypothesis
instead of the climb. -/
theorem gst_power_two_wave_large_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis)
    (a : Nat) (ha : 500 < a) : GSTPowerTwoWave a := by
  have hMaster : GSTFourPowerOntologicalAdapter.FourPowerCreationMaster :=
    creation_master_of_hypothesis h
  unfold GSTPowerTwoWave
  have hnav0 : GSTCanonicalTailStateIso.Navigation (4^a) :=
    GSTFourPowerOntologicalAdapter.gst_four_power_ontological_navigation_of_master
      hMaster a (by omega) (by omega)
  have hnav : GSTNavigationWitness (4^a) :=
    gst_navigation_witness_of_standalone_navigation (4^a) hnav0
  obtain ⟨p, hd, _hspace⟩ := hnav
  exact Or.inl (hasTernaryTwo_of_digit (4^a) p hd)

/-- The even case from the hypothesis: every `4^a` with `a ≥ 5` has a
ternary digit two.  Below 500 the kernel-checked modular base carries it;
above 500 the hypothesis-fed two-wave carries it.  Body identical to the
monolith's green `erdos_ternary_2_even_universal`. -/
theorem erdos_ternary_2_even_universal_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis)
    (a : Nat) (ha : 5 ≤ a) :
    hasTernaryTwo (4^a) = true := by
  by_cases ha500 : a ≤ 500
  · exact modular_check_base a ha ha500
  · have htwo : GSTPowerTwoWave a :=
      gst_power_two_wave_large_of_hypothesis h a (by omega)
    rcases htwo with hcurrent | hprevious
    · exact hcurrent
    · obtain ⟨p, hd, hspace⟩ := hprevious
      have hp : 1 ≤ p := by
        cases p with
        | zero =>
            simp only [gstDigit, Nat.pow_zero, Nat.div_one] at hd
            have hmod : 4^(a-1) % 3 = 1 := by
              rw [Nat.pow_mod]
              simp
            omega
        | succ p => omega
      have hCmod : gstCarry (4^(a-1)) p % 3 = 0 :=
        gstGoodSpace_carry_mod3_zero (4^(a-1)) p hspace
      have hClt : gstCarry (4^(a-1)) p < 4 :=
        gstCarry_lt_four (4^(a-1)) p hp
      have hgood : gstCarry (4^(a-1)) p = 0 ∨
          gstCarry (4^(a-1)) p = 3 := by omega
      have hlift := gst_pure_lift_or_forced_cascade
        (4^(a-1)) p hp hd hgood
      have hd4 : gstDigit (4 * 4^(a-1)) p = 2 := by
        rcases hlift with h | h
        · exact h.1
        · exact h.1
      rw [gst_four_pow_adjacent a (by omega)] at hd4
      exact hasTernaryTwo_of_digit (4^a) p hd4

/-- **THE CONVERSION — THE CROWN.**  The hypothesis, stated as one explicit
`Prop` binder, yields the full Erdős ternary-2 theorem.  The hypothesis is
now a theorem's premise; the implication is the theorem.  Every `2^n`
with `n ≥ 9` has a ternary digit two, given the creation hypothesis. -/
theorem erdos_ternary_2_universal_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_even_conjecture
    (fun K hK => has_two_imp_not_no_two (4^K)
      (erdos_ternary_2_even_universal_of_hypothesis h K (by omega)))
    n hn

/-! ## Section 2 — the named core and the k=1 collision-core wire -/

/-- THE NAMED CORE — eq.(21) at canonical k=1 strength.  On the canonical
residual rectangle of `residualEnergy s 1 n`, the weighted crossing prefix
is dominated by the base-three weighted right-edge crossing sign: whenever
the right-edge weighted `crossDensity` sum is non-positive, the whole
weighted cross prefix is non-positive.  This is the ONE remaining link on
the residual route — the eq.(21) content, which is false for general
languages and is asserted here only at the canonical k=1 rectangle, where
every cell obeys the exact production `graph_cell_exact` law. -/
def GSTStep6SignClosure (s n : Nat) : Prop :=
  ∀ K : Nat,
    (Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) *
        crossDensity
          (graph (residualEnergy s 1 n) (residualWidth s) (s+2+p)).seven.carry
          (graph (residualEnergy s 1 n) (residualWidth s) (s+2+p)).seven.digit) ≤ 0) →
    weightedCrossPrefix
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.carry)
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.digit)
      (residualWidth s) K ≤ 0

/-- The canonical residual rectangle is nondegenerate: `residualWidth s = 3^s
≥ 1`. -/
theorem residualWidth_pos (s : Nat) (_hs : 1 ≤ s) : 1 ≤ residualWidth s := by
  unfold residualWidth
  have hpos : 0 < 3^s := Nat.pow_pos (by decide)
  omega

/-- **THE k=1 COLLISION-CORE WIRE.**  The production connector, the eq.(37)
right-edge sign seam and the sharp crossing positive side compose — given
the named core — into the k=1 Ω-termination: a child Navigation witness
and a complete Omega bad trace cannot coexist.  This is the theorem the
reverted revival attempted with broken automation terminals; here every
ingredient is a named green theorem and the only unstated input is the
core itself. -/
theorem gst_omega_termination_s1_of_sign_closure
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hCore : GSTStep6SignClosure s n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ¬ GSTOmegaInfiniteBadTrace s 1 n := by
  intro hbad
  -- Connector, right side: an all-depth Omega bad trace is a literal
  -- all-bad right boundary of the residual rectangle.
  have hRightBad : ∀ j,
      ¬ HappyCell
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.carry
        (graph (residualEnergy s 1 n) (residualWidth s) (s+2+j)).seven.digit :=
    GSTFinalResidualConnector.residual_bad_trace_to_right_bad
      s 1 n hs (by decide) hbad
  -- Connector, left side: the child Navigation witness is a literal
  -- Happy cell on the left boundary of the same rectangle.
  obtain ⟨q, hLeftHappy⟩ :=
    GSTFinalResidualConnector.residual_child_witness_to_left_happy
      s 1 n hs (by decide) hchild
  -- eq.(37): right-bad forces the weighted right-edge crossing sign
  -- non-positive.
  have hGamma :=
    GSTFinalPrefixOneStep6Boundary.canonical_right_bad_forces_weighted_cross_nonpositive
      s n q hs hn hRightBad
  -- THE CORE: the right-edge sign closes the weighted cross prefix.
  have hWCPle :=
    hCore (q+1) hGamma
  -- Sharp crossing positive side: the left-boundary Happy cell forces
  -- the same weighted cross prefix strictly positive.
  have hWCPpos : 0 < weightedCrossPrefix
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.carry)
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.digit)
      (residualWidth s) (q+1) :=
    weightedCrossPrefix_positive_of_top_leading_happy
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.carry)
      (fun t p => (graph (residualEnergy s 1 n) t (s+2+p)).seven.digit)
      (residualWidth s) q
      (residualWidth_pos s hs)
      (fun t p _ _ => graph_carry_lt_four (residualEnergy s 1 n) t (s+2+p))
      (fun t p _ _ => graph_digit_lt_three (residualEnergy s 1 n) t (s+2+p))
      (fun t p _ _ => (graph_cell_exact (residualEnergy s 1 n) t (s+2+p)).1)
      hLeftHappy
  omega

/-! ## Section 3 — the interconnection: hypothesis and core, one termination -/

/-- The hypothesis closes the k=1 collision through the atomic seam: POE
builds the parent Navigation witness from the master, and the monolith's
atomic Omega-bad theorem forbids every parent Navigation witness. -/
theorem gst_step6_collision_kernel_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have hparent : GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_navigation_lift_of_master_inline
      (creation_master_of_hypothesis h) s n hs hn hchild
  exact (gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
    s n hs hn hBad) hparent

/-- **THE INTERCONNECTION, STATED.**  The hypothesis closes the k=1
Ω-termination — the same termination the named core closes through the
boundary seam.  Two sockets, one termination. -/
theorem gst_omega_termination_s1_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis)
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n)) :
    ¬ GSTOmegaInfiniteBadTrace s 1 n := by
  intro hbad
  exact gst_step6_collision_kernel_of_hypothesis
    h s n hs hn hchild hbad

/-- The prefix-one lift runs on the hypothesis socket — the object the
reverted revival attempted to build without inputs.  Here it is honest:
one explicit premise, the monolith's own green lift. -/
theorem gst_prefix_one_navigation_lift_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis) :
    GSTPrefixOneNavigationLift :=
  gst_prefix_one_navigation_lift_of_master_inline
    (creation_master_of_hypothesis h)

/-- The monolith's residual induction accepts the hypothesis-fed lift:
one prefix-one lift composes into the full residual lift for every k. -/
theorem residual_navigation_lift_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis) :
    GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_prefix_one
    (gst_prefix_one_navigation_lift_of_hypothesis h)

/-- Universal canonical Navigation from the hypothesis: the monolith's
strong induction turns the residual lift into a Navigation witness for
every canonical constant with non-multiple-of-three tail. -/
theorem navigation_all_of_hypothesis
    (h : erdos_ternary_2_creation_hypothesis) :
    ∀ s b, 1 ≤ s → 1 ≤ b → b % 3 ≠ 0 → (2 ≤ s ∨ 1 < b) →
      GSTNavigationWitness (gstNavigationConstant s b) :=
  gst_navigation_witness_all_of_residual
    (residual_navigation_lift_of_hypothesis h)

/-! ## Section 4 — receipts -/

#print axioms creation_master_of_hypothesis
#print axioms gst_power_two_wave_large_of_hypothesis
#print axioms erdos_ternary_2_even_universal_of_hypothesis
#print axioms erdos_ternary_2_universal_of_hypothesis
#print axioms gst_omega_termination_s1_of_sign_closure
#print axioms gst_step6_collision_kernel_of_hypothesis
#print axioms gst_omega_termination_s1_of_hypothesis
#print axioms gst_prefix_one_navigation_lift_of_hypothesis
#print axioms residual_navigation_lift_of_hypothesis
#print axioms navigation_all_of_hypothesis

end GSTHypothesisToTheorem
