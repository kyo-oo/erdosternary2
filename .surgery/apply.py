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

# The old residual Omega termination chain is proof archaeology only.
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
    # Fix: ALL inner /- and -/ in the quarantine block close the quarantine
    # comment prematurely. Convert them to -- (regular comments).
    start_idx = text.index(qstart_tag) + len(qstart_tag)
    end_idx = text.index(qend_tag)
    inner = text[start_idx:end_idx]
    inner = inner.replace('/-', '--')
    inner = inner.replace('-/', '--')
    text = text[:start_idx] + inner + text[end_idx:]

# ---------------------------------------------------------------------------
# Attach the theorem-grade BIG-N/origin/right-chord stack before the production
# seam. We follow only local snapshot imports, strip imports/headers, and emit
# each module once in dependency order. ErdosTernary2.lean stays the sole target.
# ---------------------------------------------------------------------------
attach_marker = '-- BEGIN ATTACHED SOL BIG-N CLOSURE STACK\n'
attach_end = '-- END ATTACHED SOL BIG-N CLOSURE STACK\n\n'
anchor = '''/-\n  INLINE INTEGRATION TARGET.\n'''
decidable_code = "-- Concrete Decidable instances for custom defs\n" \
    "instance : Decidable (GSTBadPairS (C : Nat) (d : Nat)) :=" \
    "  if h : d = 2 \\\<and> (C = 0 \\\<or> C = 3) then isFalse h else isTrue h\n\n"

if attach_marker not in text:
    snap = Path('ker07-snapshot/branches/16_sol_latest__5c579-final-bigN-right-chord-atomic')
    roots = [
        'AtomicPrefixOneReductionScratch',
        'CanonicalCausalityScratch',
        'CanonicalOriginCutIntersectionScratch',
        'ResidualNullBranchReductionScratch',
        'ResidualNullTerminalScratch',
        'ResidualNullPrefixFourCutScratch',
        'RetainedOffsetUStateScratch',
        'CanonicalOriginTritForcingScratch',
        'CanonicalResidualInfiniteSupportBridgeScratch',
        'PrefixOneTwoDigitChordScratch',
        'RightChordCanonicalGateScratch',
        'CanonicalRightChordTrapScratch',
        'CanonicalPhaseCrossingSurgeryScratch',
        'InformationFluxScratch',
        'StripConservationScratch',
        'HandwrittenSignedKernelFluxScratch',
        'HandwrittenBigNOmegaScratch',
        'HandwrittenBigNBinaryFactorScratch',
        'HandwrittenBig1PathProjectorScratch',
        'HandwrittenOmegaOriginCommutingSquareScratch',
    ]
    seen = set()
    chunks = []

    def visit(mod: str):
        if mod in seen or mod in {'Mathlib', 'ErdosTernary2'}:
            return
        path = snap / f'{mod}.lean'
        if not path.exists():
            return
        seen.add(mod)
        src_lines = path.read_text(encoding='utf-8').splitlines()
        deps = []
        last_import = -1
        for i, line in enumerate(src_lines):
            stripped = line.strip()
            if stripped.startswith('import '):
                deps.extend(stripped[len('import '):].split())
                last_import = i
        for dep in deps:
            visit(dep)
        body_lines = src_lines[last_import + 1:] if last_import >= 0 else src_lines
        body = '\n'.join(body_lines).strip() + '\n'
        chunks.append(
            f'-- BEGIN ATTACHED {mod}.lean\n'
            + body
            + f'-- END ATTACHED {mod}.lean\n\n'
        )

    for root in roots:
        visit(root)

    attached = attach_marker + ''.join(chunks) + attach_end
    if anchor not in text:
        raise RuntimeError('inline integration anchor missing for BIG-N attachment')
    text = text.replace(anchor, decidable_code + attached + anchor, 1)

# BIG-N finite endpoint. This is the literal finite i=N case: a carry-three
# start cannot reach carry one through an all-BIG1 information interval.
bign_code = r'''/-- BIG-N finite endpoint adapter. -/
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

/-- Literal BIG-N finite-support horizon for the canonical child information. -/
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

'''
if 'theorem gst_bigN_seed3_endpoint_forces_non_one_inline' not in text:
    if anchor not in text:
        raise RuntimeError('BIG-N insertion anchor missing')
    text = text.replace(anchor, bign_code + anchor, 1)

# Factor the child origin n = 3^r*m. Every already-closed origin class now
# contradicts parent Omega badness immediately. The only remaining point is the
# genuine 3-free young residual where the attached BIG-N/right-chord stack acts.
info_start_marker = 'theorem gst_prefix_one_information_bad_descends_inline'
info_end_marker = '\n\n/-- Corrected information-wave closure:'
info_start = text.index(info_start_marker)
info_end = text.index(info_end_marker, info_start)
new_info = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  have hnoParent :
      ¬ GSTNavigationWitness (gstNavigationConstant s (1 + 3*n)) :=
    gst_prefix_one_no_parent_navigation_of_omega_bad_atomic s n hs hn hBad

  let r := v3 n
  let m := n / 3^r
  have hnpos : 0 < n := by omega
  have hdvd : 3^r ∣ n := by
    dsimp [r]
    exact pow_v3_dvd n hnpos
  have hmod : n % 3^r = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hnfac : n = 3^r * m := by
    dsimp [m]
    have h := Nat.div_add_mod n (3^r)
    rw [hmod, Nat.add_zero] at h
    exact h.symm
  have hmne : m ≠ 0 := by
    intro hmz
    have hnzero : n = 0 := by simpa [hmz] using hnfac
    omega
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmne
  have hm3 : m % 3 ≠ 0 := by
    dsimp [m, r]
    exact v3_maximal n hnpos

  have hscale :
      gstNavigationConstant (s+1) n =
        3^r * gstNavigationConstant (s+1+r) m := by
    rw [hnfac]
    exact gst_navigation_constant_mul3_pow_atomic (s+1) r m (by omega)
  rw [hscale] at hchild
  have hchildCore :
      GSTNavigationWitness (gstNavigationConstant (s+1+r) m) :=
    gstNavigationWitness_of_mul_three_pow_atomic r
      (gstNavigationConstant (s+1+r) m) hchild

  let k := r + 1
  have hk : 1 ≤ k := by dsimp [k]; omega
  have hparentArg : 1 + 3*n = 1 + 3^k*m := by
    dsimp [k]
    rw [hnfac, Nat.pow_succ]
    ring

  by_cases hclosed : GSTOriginClosed s k (m % 3)
  · have hparentCore :
        GSTNavigationWitness (gstNavigationConstant s (1 + 3^k*m)) :=
      gst_navigation_constant_origin_closed_witness
        s k m (m % 3) hs hm hm3 rfl hclosed
    apply hnoParent
    rw [hparentArg]
    exact hparentCore

  have hrange : m % 3 = 1 ∨ m % 3 = 2 := by
    have hlt : m % 3 < 3 := Nat.mod_lt _ (by decide)
    omega
  have hboundary : GSTResidualBoundary s k (m % 3) :=
    gst_origin_not_closed_boundary s k (m % 3) hs hk hrange hclosed

  -- TRUE RED SEAM. Everything used by BIG-N Step 6 is now physically in the
  -- monolith: hchildCore, hBad, hboundary, retained-origin recursion,
  -- right-chord, physical rectangle, signed flux, and finite i=N horizon.
  gst_omega'''
text = text[:info_start] + new_info + text[info_end:]

p.write_text(text, encoding='utf-8')
