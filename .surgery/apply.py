from pathlib import Path

p = Path('ErdosTernary2.lean')
text = p.read_text(encoding='utf-8')

# Parser repair is intentionally idempotent. Later proof incisions are made
# only against exact anchors in the canonical monolith; no snapshot proof file
# is ever substituted for ErdosTernary2.lean.
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

# The three residual Ω theorems are explicitly labelled legacy overproof in
# the canonical source.  Quarantine that inactive architecture so the compiler
# exposes the one modern prefix-one information seam instead of three aliases
# of the same missing phase-crossing argument.
qtag = 'QUARANTINED LEGACY RESIDUAL OMEGA START'
if qtag not in text:
    qstart_marker = '/-- First-level residual Ω∞ termination.'
    qend_marker = '\n/-\n/-- Numerical ceiling used to bound every power-of-four graph witness.'
    qstart = text.index(qstart_marker)
    qend = text.index(qend_marker, qstart)
    legacy = text[qstart:qend]
    text = (
        text[:qstart]
        + '/- ' + qtag + '\n'
        + legacy
        + '\nQUARANTINED LEGACY RESIDUAL OMEGA END -/\n'
        + text[qend:]
    )

# The active information-descent theorem was circularly rebuilding a parent
# Navigation witness through the quarantined legacy residual theorem. Replace
# that body by the deliberate gst_omega call-site. This is the red test for the
# new GST-specific tactic: one exact theorem, one exact phase-crossing seam.
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
