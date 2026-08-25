#!/usr/bin/env python3
from pathlib import Path

p = Path('ErdosTernary2.lean')
s = p.read_text(encoding='utf-8')

# Keep the packaging behavior of the forward generator that already compiled
# the monolith through the prefix-one seam.  Do not remove attached packets or
# their declarations here.
imp = 'import GSTGraphV2InfiniteControl\n'
if imp not in s:
    anchor = 'import Mathlib.Tactic.Ring\n'
    if anchor not in s:
        raise SystemExit('import anchor not found')
    s = s.replace(anchor, anchor + imp, 1)

start_marker = '/-- Literal BIG-N finite-support horizon for the canonical child information. -/'
end_marker = '/-- The two consecutive power waves overlap at a Happy Gate.'
installed_marker = '-- SOL56 DIRECT RESIDUAL-LIFT PREFIX-ONE CLOSURE'

if start_marker not in s:
    if installed_marker in s:
        print('direct residual-lift atomic replacement already installed')
        p.write_text(s, encoding='utf-8')
        raise SystemExit(0)
    raise SystemExit('old prefix-one start marker not found')
if end_marker not in s:
    raise SystemExit('prefix-one end marker not found')

start = s.index(start_marker)
end = s.index(end_marker, start)

replacement = r'''/-- Literal BIG-N finite-support horizon for the canonical child information. -/
theorem gst_prefix_one_bigN_future_zero_inline
    (s n : Nat) (hs : 1 ≤ s) :
    let N := gstNavigationConstant (s+1) n
    N / 3^N = 0 := by
  dsimp only
  by_cases hN0 : gstNavigationConstant (s+1) n = 0
  · rw [hN0]
    decide
  · exact gst_navigation_self_horizon_zeroS
      (gstNavigationConstant (s+1) n) (by omega)

-- SOL56 DIRECT RESIDUAL-LIFT PREFIX-ONE CLOSURE
/-- Prefix-one information descent by direct residual normalization.
A child Navigation witness is stripped of the exact 3-adic content of the
origin.  The normalized residual witness then lifts to the forbidden parent
Navigation witness, contradicting the Omega-infinite bad trace. -/
theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

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
    · exact gst_residual_navigation_lift
        s (r+1) m hs (by omega) hm hm3 hclosed hchildNorm

  have harg : 1 + 3^(r+1)*m = 1 + 3*n := by
    rw [Nat.pow_succ, hnshape]
    ring
  have hparent :
      GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) := by
    rw [← harg]
    exact hparentNorm
  exact hnoParent hparent

/-- Corrected information-wave closure: once parent badness descends to the
shared child information, the certified child Happy Gate is an immediate
contradiction. -/
theorem gst_prefix_one_child_gate_contradicts_parent_bad_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (data : GSTPrefixOneOmegaData s n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) : False := by
  have hChildBad : GSTCompleteBadTrace (gstNavigationConstant (s+1) n) :=
    gst_prefix_one_information_bad_descends_inline s n hs hn hBad
  have hAt := hChildBad data.childGateIndex
  have hGate :
      gstDigit (gstNavigationConstant (s+1) n) data.childGateIndex = 2 ∧
      (gstCarry (gstNavigationConstant (s+1) n) data.childGateIndex = 0 ∨
       gstCarry (gstNavigationConstant (s+1) n) data.childGateIndex = 3) := by
    simpa only [gstOmega] using data.childGate
  exact hAt hGate

/-- Public prefix-one theorem: parent failure supplies the exact bad trace, and
the direct residual-lift information theorem contradicts the certified child
gate. -/
theorem gst_prefix_one_navigation_lift :
    GSTPrefixOneNavigationLift := by
  intro s n hs hn hchild
  by_contra hnoParent
  have hBad : GSTOmegaInfiniteBadTrace s 1 n :=
    gst_prefix_one_omega_bad_of_no_parent_navigation_inline s n hs hnoParent
  let data : GSTPrefixOneOmegaData s n :=
    gst_prefix_one_omegaData s n hs hchild
  exact gst_prefix_one_child_gate_contradicts_parent_bad_inline
    s n hs hn data hBad

#print axioms gst_prefix_one_information_bad_descends_inline
#print axioms gst_prefix_one_navigation_lift

'''

s = s[:start] + replacement + s[end:]

# RC2 mechanical scar already established by the forward compiler frontier.
old_ring = 'convert hshared using 1 <;> ring'
ring_count = s.count(old_ring)
if ring_count != 1:
    raise SystemExit(f'expected exactly one localized ring scar, found {ring_count}')
s = s.replace(old_ring, 'convert hshared using 1 <;> ring_nf', 1)

# Hard guards: the live output must not reintroduce the obsolete creation or
# collision route.
for forbidden in (
    'theorem gst_h_creation_full_power_navigation_atomic',
    'theorem gst_full_power_navigation_descends_atomic',
    'theorem gst_prefix_one_u2d_atomic_collision_inline',
):
    if forbidden in s:
        raise SystemExit(f'obsolete live theorem survived direct replacement: {forbidden}')
if 'h_creation_for_4pow' in s[start:s.index(end_marker, start) if end_marker in s[start:] else len(s)]:
    raise SystemExit('legacy h_creation dependency survived direct replacement block')
if 'trace_state\n  contradiction' in s:
    raise SystemExit('old RED seam survived direct replacement')

p.write_text(s, encoding='utf-8')
print('DIRECT_PREFIX_ONE_RESIDUAL_REPLACEMENT=1')
print('LIVE_LEGACY_H_CREATION_DEPENDENCY=0')
print('COLLISION_HELPER_REMOVED=1')
print('forward mechanical RC2 fixes installed')
