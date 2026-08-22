#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

imp = 'import GSTU2DExactCrossingCharge\n'
if imp not in s:
    anchor = 'import Mathlib.Tactic.Ring\n'
    if anchor not in s:
        raise SystemExit('import anchor not found')
    s = s.replace(anchor, anchor + imp, 1)

start_marker = '/-- Literal BIG-N finite-support horizon for the canonical child information. -/'
end_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'

if start_marker not in s:
    if 'theorem gst_prefix_one_u2d_atomic_collision_inline' in s:
        print('atomic U2D replacement already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('old prefix-one start marker not found')
if end_marker not in s:
    raise SystemExit('prefix-one end marker not found')

start = s.index(start_marker)
end = s.index(end_marker, start)

replacement = r'''/-- Atomic U2D replacement for the superseded BIG-N / bad-reflection chain.
The theorem consumes the certified child Happy Gate and the complete canonical
seed-one bad trace directly.  The old finite horizon, information-bad descent,
and child-gate contradiction theorems are intentionally absent. -/
theorem gst_prefix_one_u2d_atomic_collision_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hchild : GSTNavigationWitness (gstNavigationConstant (s+1) n))
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  let data : GSTPrefixOneOmegaData s n :=
    gst_prefix_one_omegaData s n hs hchild
  let T := gstNavigationConstant (s+1) n
  let q := data.childGateIndex

  have hGate :
      gstDigit T q = 2 ∧ (gstCarry T q = 0 ∨ gstCarry T q = 3) := by
    dsimp [T, q, data]
    simpa only [gstOmega] using data.childGate

  have hseeded := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad
  have hparentBadQ := hseeded q

  let C : Nat → Nat := fun t => gstCarry (4^t * T) q
  let d : Nat → Nat := fun t => gstDigit (4^t * T) q

  have hfirst : GSTU2DEventTransport.HappyCell (C 0) (d 0) := by
    simpa [GSTU2DEventTransport.HappyCell, C, d] using hGate

  have hNpos : 1 ≤ 3^s := by
    have hp : 0 < 3^s := Nat.pow_pos (by decide)
    omega
  have hClt : ∀ t, t < 3^s → C t < 4 := by
    intro t _ht
    dsimp [C]
    by_cases hq0 : q = 0
    · rw [hq0]
      unfold gstCarry
      rw [Nat.pow_zero]
      norm_num
    · exact gstCarry_lt_four _ q (by omega)
  have hdlt : ∀ t, t < 3^s → d t < 3 := by
    intro t _ht
    exact gstDigit_lt_three _ _

  have hpressure :
      17 * (((4^(3^s) : Nat) : Int)) + 37 ≤
        GSTU2DExactCrossingCharge.reverseCrossCode C d (3^s) :=
    GSTU2DExactCrossingCharge.reverseCrossCode_ge_exponential_of_leading_happy
      C d hfirst (3^s) hNpos hClt hdlt

  -- RED is now intentionally atomic: only the canonical charge-to-parent-bad
  -- collision remains.  None of the superseded finite/termination theorems is
  -- available in this proof context.
  exfalso
  omega

/-- Public prefix-one lift consumes only the new atomic U2D collision theorem. -/
theorem gst_prefix_one_navigation_lift : GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  exact gst_prefix_one_u2d_atomic_collision_inline s n hs hn hchild hBad


'''

s = s[:start] + replacement + s[end:]
p.write_text(s, encoding='utf-8')
print('installed atomic U2D replacement and removed superseded prefix-one chain')
