#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

needle = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

replacement = '''  -- Direct residual bridge probe.  First recover the exact generalized
  -- Omega bad trace from the already-proved absence of a parent Navigation
  -- witness.  This does not use the quarantined residual termination theorem.
  have hResidualBad : GSTOmegaInfiniteBadTrace s k m := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
    intro hzero
    apply hnoParent
    rw [hparentArg]
    exact gst_omega_gate_zero_closes_parent s k m hs ⟨j, hzero⟩

  -- Normalize the child level once.  Here k = r+1, hence s+k = s+1+r.
  -- Keeping this as an explicit kernel equality avoids relying on elaborator
  -- associativity during every downstream application.
  have hchildCoreK :
      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by
    simpa [k, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hchildCore

  -- Keep the actual child gate and every exact coupled coordinate live.  This
  -- is the minimal context used by the old arithmetic solver, but here it is
  -- reconstructed directly at the production seam rather than importing any
  -- quarantined residual theorem.
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

  -- RED probe: if the current exact arithmetic context already closes, this
  -- produces an ordinary kernel term.  Otherwise CI reports the irreducible
  -- residual context and we refine only that branch.
  gst_omega
'''

if needle not in s:
    raise SystemExit('production gst_end seam not found')

s = s.replace(needle, replacement, 1)
p.write_text(s, encoding='utf-8')
print('installed direct residual bridge probe')
