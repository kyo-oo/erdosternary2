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

# If an earlier diagnostic run quarantined the residual Ω chain, restore it.
# The exact parent-witness proof below consumes this chain directly.
qstart_tag = '/- QUARANTINED LEGACY RESIDUAL OMEGA START\n'
qend_tag = '\nQUARANTINED LEGACY RESIDUAL OMEGA END -/'
if qstart_tag in text:
    text = text.replace(qstart_tag, '', 1)
    text = text.replace(qend_tag, '', 1)

# Atomic information-descent splice.  Rather than asking gst_omega to invent
# the phase crossing at this late call-site, use the already formalized
# residual Ω termination -> residual Navigation lift, project the resulting
# parent Happy Gate into the Ω cell, and contradict the complete Ω bad trace.
info_start_marker = 'theorem gst_prefix_one_information_bad_descends_inline'
info_end_marker = '\n\n/-- Corrected information-wave closure:'
info_start = text.index(info_start_marker)
info_end = text.index(info_end_marker, info_start)
new_info = '''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  have hb : 1 ≤ 1 + 3*n := by omega
  have hb3 : (1 + 3*n) % 3 ≠ 0 := by omega
  have hdomain : 2 ≤ s ∨ 1 < 1 + 3*n := Or.inr (by omega)
  have hParent : GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_navigation_witness_all_of_residual
      (gst_residual_navigation_lift_of_omega_termination
        gst_residual_omega_termination)
      s (1 + 3*n) hs hb hb3 hdomain
  rcases hParent with ⟨j, hd, hspace⟩
  cases j with
  | zero =>
      have hmod := gstNavigationConstant_mod3 s (1 + 3*n) hs hb hb3
      have hbmod : (1 + 3*n) % 3 = 1 := by omega
      simp only [gstDigit, Nat.pow_zero, Nat.div_one] at hd
      rw [hmod, hbmod] at hd
      omega
  | succ j =>
      have hprojection := gst_omega_parent_projection s 1 n j hs
      have hCmod : gstCarry (gstNavigationConstant s (1 + 3*n)) (j+1) % 3 = 0 := by
        exact gstGoodSpace_carry_mod3_zero _ (j+1) hspace
      have hClt : gstCarry (gstNavigationConstant s (1 + 3*n)) (j+1) < 4 :=
        gstCarry_lt_four _ (j+1) (by omega)
      have hC : gstCarry (gstNavigationConstant s (1 + 3*n)) (j+1) = 0 ∨
          gstCarry (gstNavigationConstant s (1 + 3*n)) (j+1) = 3 := by
        omega
      have hd' : gstDigit (gstNavigationConstant s (1 + 3*n)) (1+j) = 2 := by
        simpa [Nat.add_comm] using hd
      have hC' : gstCarry (gstNavigationConstant s (1 + 3*n)) (1+j) = 0 ∨
          gstCarry (gstNavigationConstant s (1 + 3*n)) (1+j) = 3 := by
        simpa [Nat.add_comm] using hC
      have hgate :
          (gstOmega s 1 n j).parentDigit = 2 ∧
          ((gstOmega s 1 n j).parentCarry = 0 ∨
           (gstOmega s 1 n j).parentCarry = 3) := by
        constructor
        · rw [← hprojection.1]
          simpa [Nat.pow_one] using hd'
        · rw [← hprojection.2]
          simpa [Nat.pow_one] using hC'
      have hzero : GSTOmegaGatePolynomial (gstOmega s 1 n j) = 0 :=
        (gst_omega_gate_polynomial_zero_iff (gstOmega s 1 n j)).2 hgate
      have hne := hBad j
      change GSTOmegaGatePolynomial (gstOmega s 1 n j) ≠ 0 at hne
      exact False.elim (hne hzero)'''
text = text[:info_start] + new_info + text[info_end:]

p.write_text(text, encoding='utf-8')
