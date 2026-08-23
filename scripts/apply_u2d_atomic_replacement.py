#!/usr/bin/env python3
from pathlib import Path
import re

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

raw_lines = len(s.splitlines())
raw_theorems = len(re.findall(r'(?m)^\s*(?:private\s+)?theorem\s+', s))
raw_defs = len(re.findall(r'(?m)^\s*(?:noncomputable\s+)?def\s+', s))
print(f'PRODUCTION_STATS raw_lines={raw_lines} raw_theorems={raw_theorems} raw_defs={raw_defs}')

# Keep the existing production proof and splice only the true residual seam.
# The unified graph / rectangle modules are compiled independently by CI and
# imported here so the production proof is checked in the same environment.
for imp in [
    'import GSTGraphV2InfiniteControl\n',
    'import GSTU2DPureDivergence83\n',
    'import GSTGraphV2UnifiedPowerRectangle\n',
    'import GSTGraphV2UnifiedVerticalTelescope\n',
    'import GSTGraphV2PerfectPowerAncestry\n',
]:
    if imp not in s:
        anchor = 'import Mathlib.Tactic.Ring\n'
        if anchor not in s:
            raise SystemExit('import anchor not found')
        s = s.replace(anchor, anchor + imp, 1)

needle = '''  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_end
'''

if needle not in s:
    if 'have hBadResidual : GSTOmegaInfiniteBadTrace s k m := by' in s and '\n  gst_end\n' not in s:
        print('residual-only atomic surgery already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('literal residual gst_end seam not found')

replacement = r'''  -- Atomic infinite-graph surgery.  The proof above has already removed every
  -- origin state that closes immediately.  Reindex the no-parent statement
  -- to the exact residual Ω(s,k,m) graph; no terminal/support argument enters.
  have hnoResidual :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) := by
    intro hparentCore
    apply hnoParent
    rw [hparentArg]
    exact hparentCore

  have hBadResidual : GSTOmegaInfiniteBadTrace s k m := by
    intro j
    change GSTOmegaGatePolynomial (gstOmega s k m j) ≠ 0
    intro hzero
    apply hnoResidual
    exact gst_omega_gate_zero_closes_parent s k m hs ⟨j, hzero⟩

  have hsk : s + k = s + 1 + r := by
    dsimp [k]
    omega
  have hchildResidual :
      GSTNavigationWitness (gstNavigationConstant (s+k) m) := by
    rw [hsk]
    exact hchildCore

  obtain ⟨j, hj⟩ :=
    gst_omega_childZeroSet_nonempty_of_navigation_witness s k m hchildResidual
  have hbadChild := hBadResidual j
  have horigin := gst_omega_origin_exact s k m j hs
  have hstep := gst_omega_universal_equation s k m j
  have hdescent := gst_residual_origin_descent_certificate
    s k m hs hk hm
  have hseeded :=
    (gst_omega_infiniteBadTrace_iff_seededAffine s k m).1 hBadResidual
  have heecho := gst_omega_affine_tail_block_echo s k m hs
  have hblocks : ∀ q, GSTOmegaBadBlock s k m q :=
    gst_omega_infiniteBadTrace_blocks s k m hBadResidual

  -- Unified-graph certificate for the exact same canonical power rectangle.
  let Eres : Nat := 4^(3^(s+k) * m)
  let Nres : Nat := 3^s
  have hNres : 1 ≤ Nres := by
    dsimp [Nres]
    exact Nat.one_le_pow _ _ (by decide)
  have hunified :=
    GSTGraphV2UnifiedVerticalTelescope.unified_equationIII_graph_closed
      Eres Nres (s+k+1+j)
  have hphysical :=
    GSTGraphV2UnifiedPowerRectangle.unifiedState_physicalInvariant
      Eres Nres (s+k+1+j)
  have hdensity :=
    GSTU2DPureDivergence83.graph_density83_rectangle_exact
      Eres Nres (s+k+2+j)

  simp only [GSTOmegaBadSet, Set.mem_setOf_eq] at hbadChild

  -- TEMPORARY RED ENDPOINT: this is the one infinite-graph closure now being
  -- replaced by the conserved perfect-power block transfer theorem.
  rcases hboundary with hS1 | hS3 | hStable
  · rcases hS1 with ⟨hs1, hcase⟩
    subst s
    simp_all only [GSTOmegaChildZeroSet, GSTOmegaBadSet,
      GSTOmegaBadBlock, GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> first | contradiction | omega
  · rcases hS3 with ⟨hs3, hk7, h21, h41, h62⟩
    subst s
    simp_all only [GSTOmegaChildZeroSet, GSTOmegaBadSet,
      GSTOmegaBadBlock, GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> first | contradiction | omega
  · rcases hStable with ⟨hs2, hs3, hk4, h21⟩
    simp_all only [GSTOmegaChildZeroSet, GSTOmegaBadSet,
      GSTOmegaBadBlock, GSTSeededAffineBadTrace, Set.mem_setOf_eq]
    <;> first | contradiction | omega
'''

s = s.replace(needle, replacement, 1)
p.write_text(s, encoding='utf-8')
transformed_lines = len(s.splitlines())
transformed_theorems = len(re.findall(r'(?m)^\s*(?:private\s+)?theorem\s+', s))
transformed_defs = len(re.findall(r'(?m)^\s*(?:noncomputable\s+)?def\s+', s))
print(f'PRODUCTION_STATS transformed_lines={transformed_lines} transformed_theorems={transformed_theorems} transformed_defs={transformed_defs}')
print('installed residual-only unified Graph-V2 atomic surgery')