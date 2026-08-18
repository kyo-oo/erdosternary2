from pathlib import Path

p = Path('ErdosTernary2.lean')
text = p.read_text(encoding='utf-8')

# Keep the historical header parser-safe. This edit is idempotent.
lines = text.splitlines(keepends=True)
end = None
for i, line in enumerate(lines[:80]):
    if line.strip() == '/- ====================================================================== -/':
        end = i
        break
if end is not None:
    for i in range(end + 1):
        if lines[i].startswith('/-'):
            lines[i] = '--' + lines[i][2:]
    text = ''.join(lines)

# The residual Omega termination chain is proof archaeology: quarantine it.
qstart_tag = '/- QUARANTINED LEGACY RESIDUAL OMEGA START\n'
qend_tag = '\nQUARANTINED LEGACY RESIDUAL OMEGA END -/'
legacy_start = '/-- First-level residual Ω∞ termination.'
legacy_end = '''theorem gst_residual_navigation_lift : GSTResidualNavigationLift :=
  gst_residual_navigation_lift_of_omega_termination
    gst_residual_omega_termination'''
if qstart_tag not in text:
    if legacy_start not in text or legacy_end not in text:
        raise RuntimeError('legacy residual Omega anchors missing')
    text = text.replace(legacy_start, qstart_tag + legacy_start, 1)
    text = text.replace(legacy_end, legacy_end + qend_tag, 1)

# BIG-N endpoint adapter.  This is the constructive form consumed by the
# prefix-one recursion: seed-3 at the selected physical start and carry-1 at
# the finite BIG-N horizon cannot be connected by an all-BIG1 information word.
bign_anchor = '''/-\n  INLINE INTEGRATION TARGET.\n'''
bign_code = r'''/-- BIG-N finite endpoint adapter.  If the selected physical information
    path starts in carry three and reaches carry one at the finite BIG-N
    horizon, some intervening ternary information row is not BIG1. -/
theorem gst_bigN_seed3_endpoint_forces_non_one_inline
    (R start N : Nat) (hstart_lt : start < N)
    (hstart_pos : 1 ≤ start)
    (hC_start_3 : gstCarry R start = 3)
    (hC_N_1 : gstCarry R N = 1) :
    ∃ j, start ≤ j ∧ j < N ∧ gstDigit R j ≠ 1 := by
  by_contra hnone
  have hall : ∀ j, start ≤ j → j < N → R / 3^j % 3 = 1 := by
    intro j hj0 hjN
    by_contra hne
    apply hnone
    exact ⟨j, hj0, hjN, by simpa [gstDigit] using hne⟩
  exact all_ones_imp_c1_false R start N hstart_lt hstart_pos
    (by simpa [gstCarry] using hC_start_3)
    (by simpa [gstCarry] using hC_N_1) hall

'''
if 'theorem gst_bigN_seed3_endpoint_forces_non_one_inline' not in text:
    if bign_anchor not in text:
        raise RuntimeError('BIG-N insertion anchor missing')
    text = text.replace(bign_anchor, bign_code + bign_anchor, 1)

# Restore the one real RED seam. No legacy termination theorem is consumed.
info_start_marker = 'theorem gst_prefix_one_information_bad_descends_inline'
info_end_marker = '\n\n/-- Corrected information-wave closure:'
info_start = text.index(info_start_marker)
info_end = text.index(info_end_marker, info_start)
new_info = '''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  gst_omega'''
text = text[:info_start] + new_info + text[info_end:]

p.write_text(text, encoding='utf-8')
