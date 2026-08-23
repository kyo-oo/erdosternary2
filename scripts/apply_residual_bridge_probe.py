#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

needle = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

replacement = '''  -- Direct residual bridge: recover generalized parent badness without any
  -- quarantined residual theorem.
  have hResidualBad : GSTOmegaInfiniteBadTrace s k m := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
    intro hzero
    apply hnoParent
    rw [hparentArg]
    exact gst_omega_gate_zero_closes_parent s k m hs ⟨j, hzero⟩

  have hchildCoreK :
      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by
    simpa [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchildCore

  obtain ⟨j, hj⟩ :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness s k m hchildCoreK
  have hbadChild := hResidualBad j
  have horigin := gst_omega_origin_exact s k m j hs
  have hstep := gst_omega_universal_equation s k m j
  have hdescent := gst_residual_origin_descent_certificate s k m hs hk hm
  have hseeded :=
    (gst_omega_infiniteBadTrace_iff_seededAffine s k m).1 hResidualBad
  have heecho := gst_omega_affine_tail_block_echo s k m hs
  have hblocks : ∀ q, GSTOmegaBadBlock s k m q :=
    gst_omega_infiniteBadTrace_blocks s k m hResidualBad
  simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild

  -- Split the exact residual classifier before doing any local arithmetic.
  -- This prevents the unbounded first-level family from exploding simp in the
  -- bounded level-three/stable young-cut cases.
  rcases hboundary with hfirst | hthree | hstable
  · rcases hfirst with ⟨hs1, hr1 | hr2⟩
    · subst s
      have hm1 : m % 3 = 1 := hr1
      -- HARD FAMILY: first level, residue one, arbitrary cascade depth.
      -- Keep a compiler-visible marker so the next RED result is unambiguous.
      trace_state
      gst_omega
    · rcases hr2 with ⟨hm2, hk1 | hk3⟩
      · subst s
        have hk_eq : k = 1 := hk1
        have hm2' : m % 3 = 2 := hm2
        subst k
        gst_omega
      · subst s
        have hk_eq : k = 3 := hk3
        have hm2' : m % 3 = 2 := hm2
        subst k
        gst_omega
  · rcases hthree with ⟨hs3, hk7, hne2, hne4, hne6⟩
    subst s
    interval_cases k <;> gst_omega
  · rcases hstable with ⟨hs2, hsne3, hk4, hne2⟩
    interval_cases k <;> gst_omega
'''

if needle not in s:
    raise SystemExit('production gst_end seam not found')

s = s.replace(needle, replacement, 1)
p.write_text(s, encoding='utf-8')
print('installed boundary-split residual bridge probe')
