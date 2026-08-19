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

# LEGACY BLOCK KEPT — do NOT quarantine

# ---------------------------------------------------------------------------
# Attach the theorem-grade BIG-N/origin/right-chord stack before the production
# seam. We follow only local snapshot imports, strip imports/headers, and emit
# each module once in dependency order. ErdosTernary2.lean stays the sole target.
# ---------------------------------------------------------------------------
attach_marker = '-- BEGIN ATTACHED SOL BIG-N CLOSURE STACK\n'
attach_end = '-- END ATTACHED SOL BIG-N CLOSURE STACK\n\n'
anchor = '''/-\n  INLINE INTEGRATION TARGET.\n'''
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
    text = text.replace(anchor, attached + anchor, 1)

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

# CALL SITE KEPT — do NOT replace

p.write_text(text, encoding='utf-8')
