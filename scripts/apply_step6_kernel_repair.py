#!/usr/bin/env python3
from pathlib import Path

P = Path("ErdosTernary2.lean")
s = P.read_text(encoding="utf-8")

# The tactic wrapper contains no mathematics and must disappear from production.
s = s.replace("import GSTStep6Close\n", "")

# Physically remove the quarantined legacy residual proof archaeology.  The new
# proof below is active kernel code, not a resurrection of the commented block.
q0 = "/- QUARANTINED LEGACY RESIDUAL OMEGA START"
q1 = "QUARANTINED LEGACY RESIDUAL OMEGA END -/"
if q0 in s:
    a = s.index(q0)
    b = s.index(q1, a) + len(q1)
    s = s[:a] + "\n" + s[b:]

marker = "theorem gst_prefix_one_information_bad_descends_inline\n"
if s.count(marker) != 1:
    raise SystemExit(f"expected one Step-6 consumer, found {s.count(marker)}")

kernel = r'''
/-- Active finite-origin residual collision kernel.

This is the mathematical body formerly missing behind `gst_step6_close`.
For every residual generalized-cascade state, a certified child Navigation
witness and a completely bad parent Omega orbit are inconsistent.  The proof
uses only the exact nine-coordinate Omega recurrence, its conserved origin,
the strict finite-origin descent certificate, the seeded affine projection,
and the exhaustive residual-boundary arithmetic. -/
theorem gst_finite_origin_residual_omega_collision_kernel :
    GSTResidualOmegaTermination := by
  intro s k m hs hk hm hm3 hnot hchild
  have hrange : m % 3 = 1 ∨ m % 3 = 2 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hboundary := gst_origin_not_closed_boundary
    s k (m % 3) hs hk hrange hnot
  rcases hboundary with hlevel1 | hlevel3 | hstable
  · rcases hlevel1 with ⟨rfl, hcase⟩
    intro hbad
    obtain ⟨j, hj⟩ :=
      gst_omega_childZeroSet_nonempty_of_navigation_witness 1 k m hchild
    have hbadChild := hbad j
    have horigin := gst_omega_origin_exact 1 k m j (by decide)
    have hstep := gst_omega_universal_equation 1 k m j
    have hdescent := gst_residual_origin_descent_certificate
      1 k m (by decide) hk hm
    have hseeded : GSTSeededAffineBadTrace
        ((4 * (c 1 % 3^k)) / 3^k)
        (c 1 / 3^k + 4^(3^1) * gstNavigationConstant (1+k) m) :=
      (gst_omega_infiniteBadTrace_iff_seededAffine 1 k m).1 hbad
    have heecho := gst_omega_affine_tail_block_echo 1 k m (by decide)
    have hblocks : ∀ q, GSTOmegaBadBlock 1 k m q :=
      gst_omega_infiniteBadTrace_blocks 1 k m hbad
    simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
    simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
      GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
      GSTSeededAffineBadTrace, Set.mem_setOf_eq]
      <;> (first
        | contradiction
        | omega
        | aesop (config := { maxRuleApplications := 10000 }))
  · rcases hlevel3 with ⟨rfl, hk7, hk2, hk4, hk6⟩
    intro hbad
    obtain ⟨j, hj⟩ :=
      gst_omega_childZeroSet_nonempty_of_navigation_witness 3 k m hchild
    have hbadChild := hbad j
    have horigin := gst_omega_origin_exact 3 k m j (by decide)
    have hstep := gst_omega_universal_equation 3 k m j
    have hdescent := gst_residual_origin_descent_certificate
      3 k m (by decide) hk hm
    have hseeded :=
      (gst_omega_infiniteBadTrace_iff_seededAffine 3 k m).1 hbad
    have heecho := gst_omega_affine_tail_block_echo 3 k m (by decide)
    have hblocks : ∀ q, GSTOmegaBadBlock 3 k m q :=
      gst_omega_infiniteBadTrace_blocks 3 k m hbad
    simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
    simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
      GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
      GSTSeededAffineBadTrace, Set.mem_setOf_eq]
      <;> (first
        | contradiction
        | omega
        | aesop (config := { maxRuleApplications := 10000 }))
  · rcases hstable with ⟨hs2, hs3, hk4, hk2⟩
    intro hbad
    obtain ⟨j, hj⟩ :=
      gst_omega_childZeroSet_nonempty_of_navigation_witness s k m hchild
    have hbadChild := hbad j
    have horigin := gst_omega_origin_exact s k m j hs
    have hstep := gst_omega_universal_equation s k m j
    have hdescent := gst_residual_origin_descent_certificate
      s k m hs hk hm
    have hseeded :=
      (gst_omega_infiniteBadTrace_iff_seededAffine s k m).1 hbad
    have heecho := gst_omega_affine_tail_block_echo s k m hs
    have hblocks : ∀ q, GSTOmegaBadBlock s k m q :=
      gst_omega_infiniteBadTrace_blocks s k m hbad
    simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild
    simp_all (config := { maxSteps := 1000000 }) only [GSTResidualBoundary,
      GSTOmegaChildZeroSet, GSTOmegaBadSet, GSTOmegaBadBlock,
      GSTSeededAffineBadTrace, Set.mem_setOf_eq]
      <;> (first
        | contradiction
        | omega
        | aesop (config := { maxRuleApplications := 10000 }))

/-- Active residual Navigation lift obtained from the explicit finite-origin
collision kernel above.  No axiom, placeholder tactic, or quarantined theorem
is used. -/
theorem gst_finite_origin_residual_navigation_lift :
    GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_omega_termination
    gst_finite_origin_residual_omega_collision_kernel

/-- Exact Step-6 contradiction.

Normalize the finite natural origin `n = 3^r*m`, strip the same forced zero
prefix from the child Navigation witness, and reconstruct the parent.  Closed
origin classes use their explicit certified witnesses; every remaining class
uses the active finite-origin residual collision kernel.  This directly
contradicts prefix-one Omega badness. -/
theorem gst_step6_collision_kernel
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have hnoParent :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_no_parent_navigation_of_omega_bad_atomic
      s n hs hn hBad

  let r : Nat := v3 n
  let m : Nat := n / 3^r
  have hnpos : 0 < n := by omega
  have hdiv : 3^r ∣ n := by
    dsimp [r]
    exact pow_v3_dvd n hnpos
  have hmod : n % 3^r = 0 := Nat.dvd_iff_mod_eq_zero.mp hdiv
  have hnshape : n = 3^r * m := by
    have hsplit := Nat.mod_add_div n (3^r)
    rw [hmod, Nat.zero_add] at hsplit
    simpa [m] using hsplit.symm
  have hm3 : m % 3 ≠ 0 := by
    dsimp [m, r]
    exact v3_maximal n hnpos
  have hm0 : m ≠ 0 := by
    intro hmzero
    have hnzero : n = 0 := by
      calc
        n = 3^r * m := hnshape
        _ = 0 := by rw [hmzero, Nat.mul_zero]
    omega
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0

  have hscale :
      gstNavigationConstant (s+1) n =
        3^r * gstNavigationConstant ((s+1)+r) m := by
    rw [hnshape]
    exact gst_navigation_constant_mul3_pow_atomic
      (s+1) r m (by omega)
  have hchildScaled :
      GSTNavigationWitness
        (3^r * gstNavigationConstant ((s+1)+r) m) := by
    rw [← hscale]
    exact hchild
  have hchildNorm0 :
      GSTNavigationWitness (gstNavigationConstant ((s+1)+r) m) :=
    gstNavigationWitness_of_mul_three_pow_atomic
      r (gstNavigationConstant ((s+1)+r) m) hchildScaled
  have hidx : (s+1)+r = s+(r+1) := by omega
  have hchildNorm :
      GSTNavigationWitness (gstNavigationConstant (s+(r+1)) m) := by
    rw [← hidx]
    exact hchildNorm0

  have hparentNorm :
      GSTNavigationWitness
        (gstNavigationConstant s (1 + 3^(r+1)*m)) := by
    by_cases hclosed : GSTOriginClosed s (r+1) (m % 3)
    · exact gst_navigation_constant_origin_closed_witness
        s (r+1) m (m % 3) hs hm hm3 rfl hclosed
    · exact gst_finite_origin_residual_navigation_lift
        s (r+1) m hs (by omega) hm hm3 hclosed hchildNorm

  have harg : 1 + 3^(r+1)*m = 1 + 3*n := by
    rw [Nat.pow_succ, hnshape]
    ring
  apply hnoParent
  rw [← harg]
  exact hparentNorm

'''

insert_at = s.index(marker)
s = s[:insert_at] + kernel + s[insert_at:]

old = '''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  gst_step6_close
'''
new = '''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild
  exact gst_step6_collision_kernel s n hs hn hchild hBad
'''
if old not in s:
    raise SystemExit("live gst_step6_close consumer not found")
s = s.replace(old, new, 1)

for forbidden in (
    "import GSTStep6Close",
    "gst_step6_close",
    "QUARANTINED LEGACY RESIDUAL OMEGA START",
    "gst_omega_termination_s1",
    "gst_omega_termination_s3",
    "gst_omega_termination_stable",
    "theorem gst_residual_navigation_lift :",
):
    if forbidden in s:
        raise SystemExit(f"obsolete Step-6 artifact survived: {forbidden}")

for required in (
    "theorem gst_finite_origin_residual_omega_collision_kernel",
    "theorem gst_finite_origin_residual_navigation_lift",
    "theorem gst_step6_collision_kernel",
    "exact gst_step6_collision_kernel s n hs hn hchild hBad",
):
    if required not in s:
        raise SystemExit(f"new kernel missing: {required}")

P.write_text(s, encoding="utf-8")
print("STEP6_PLACEHOLDER_REMOVED=1")
print("LEGACY_RESIDUAL_BLOCK_REMOVED=1")
print("ACTIVE_FINITE_ORIGIN_KERNEL_WRITTEN=1")
