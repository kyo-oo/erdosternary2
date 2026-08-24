#!/usr/bin/env python3
from pathlib import Path
import re

MAIN = Path('ErdosTernary2.lean')
BULK_BEGIN = '-- BEGIN SOL56 BULK SOURCE TRANSPLANT'
BULK_END = '-- END SOL56 BULK SOURCE TRANSPLANT'
PLACEHOLDER = '-- __SOL56_BULK_SOURCE_TRANSPLANT_PLACEHOLDER__'

# These are the production roots that the broken import-only transplant tried
# to attach to the monolith.  Their complete local dependency closure is copied
# as source into ErdosTernary2.lean; it is not left behind as an import graph.
EXPLICIT_ROOTS = [
    'GSTGraphV2ProductionLaws',
    'GSTGraphV2InfiniteControllerBridge',
    'GSTGraphV2PerfectPowerBlockProbe',
    'GSTU2DSharpCrossingBlock',
    'GSTFinalPurePowerResidueTransplant',
    'GSTPrefixOnePhaseIncidenceControl',
    'GSTPrefixOneSpacetimeIncidenceControl',
    'InformationDescentScratch',
    'InformationGeometryScratch',
    'InformationStateScratch',
    'InformationBadTraceScratch',
    'OriginTransducerScratch',
    'InformationRegenerationScratch',
    'InformationIterationScratch',
    'InformationQuotientScratch',
    'InformationLocalizationScratch',
    'InformationFluxScratch',
    'InformationForcingScratch',
    'CarryWordScratch',
    'InformationCarryWordBridgeScratch',
    'PurePowerCarrierScratch',
    'CanonicalPrefixScratch',
    'CanonicalOriginModulusScratch',
    'PrefixOneOriginPhaseRecursionScratch',
    'PurePowerBadAxisScratch',
    'BadLanguageMagnitudeScratch',
    'PurePowerTailReductionScratch',
    'HorizontalTrapWidthDescentScratch',
    'StripConservationScratch',
    'GSTGraphV2Scratch',
    'GSTGraphV2FluxScratch',
    'GSTGraphV2BlockScratch',
    'GSTExponentLiftScratch',
    'PurePowerResidueGraphScratch',
    'GSTResidueSpacetimeScratch',
    'PhaseCycleInformationScratch',
    'CanonicalCausalityScratch',
]

# These are intentionally supplied by the original monolith/header.  In
# particular ErdosPreOmega is *not* imported into the final file because its
# public arithmetic objects already occur earlier in ErdosTernary2.lean.
STOP_MODULES = {'GSTTactic', 'ErdosPreOmega', 'ErdosTernary2'}

IMPORT_RE = re.compile(r'(?m)^\s*import\s+([^\s]+)\s*$')
ATTACHED_RE = re.compile(
    r'(?ms)^-- BEGIN ATTACHED ([^\n]+\.lean)\n.*?^-- END ATTACHED \1\s*\n?'
)


def module_path(mod: str) -> Path:
    return Path(*mod.split('.')).with_suffix('.lean')


def is_external(mod: str) -> bool:
    return mod.startswith('Mathlib') or mod in STOP_MODULES


def imports_of(mod: str) -> list[str]:
    path = module_path(mod)
    if not path.exists():
        return []
    return IMPORT_RE.findall(path.read_text(encoding='utf-8'))


def sanitize_module_source(mod: str) -> str:
    path = module_path(mod)
    text = path.read_text(encoding='utf-8')
    # Import commands are illegal in the middle of the monolith and all local
    # dependencies have already been topologically placed before this body.
    text = re.sub(r'(?m)^\s*import\s+[^\n]+\n?', '', text)
    # Verification commands are useful in standalone modules but add no proof
    # content to the production monolith.
    text = re.sub(r'(?m)^\s*#check\b[^\n]*\n?', '', text)
    text = re.sub(r'(?m)^\s*#print\s+axioms\b[^\n]*\n?', '', text)
    return text.strip() + '\n'


def topo_closure(roots: list[str]) -> list[str]:
    order: list[str] = []
    perm: set[str] = set()
    temp: set[str] = set()

    def visit(mod: str) -> None:
        if is_external(mod):
            return
        path = module_path(mod)
        if not path.exists():
            return
        if mod in perm:
            return
        if mod in temp:
            raise SystemExit(f'local import cycle while transplanting: {mod}')
        temp.add(mod)
        for dep in imports_of(mod):
            visit(dep)
        temp.remove(mod)
        perm.add(mod)
        order.append(mod)

    for root in roots:
        visit(root)
    return order


s = MAIN.read_text(encoding='utf-8')

# If a previous real bulk transplant exists, remove exactly that packet and
# rebuild it from current branch sources.  Otherwise harvest the legacy
# ATTACHED packet names (the immutable Aug-23 monolith contains duplicates).
legacy_names = [m[:-5] for m in ATTACHED_RE.findall(s)]
roots = list(dict.fromkeys(EXPLICIT_ROOTS + legacy_names))
order = topo_closure(roots)
closure = set(order)
if not order:
    raise SystemExit('bulk source transplant dependency closure is empty')

if BULK_BEGIN in s:
    b0 = s.find(BULK_BEGIN)
    b1 = s.find(BULK_END, b0)
    if b1 < 0:
        raise SystemExit('unterminated existing bulk source transplant')
    b1 += len(BULK_END)
    if b1 < len(s) and s[b1] == '\n':
        b1 += 1
    s = s[:b0] + PLACEHOLDER + '\n' + s[b1:]
else:
    matches = list(ATTACHED_RE.finditer(s))
    selected = [m for m in matches if m.group(1)[:-5] in closure]
    if selected:
        pieces: list[str] = []
        pos = 0
        placed = False
        for m in selected:
            pieces.append(s[pos:m.start()])
            if not placed:
                pieces.append(PLACEHOLDER + '\n')
                placed = True
            pos = m.end()
        pieces.append(s[pos:])
        s = ''.join(pieces)
    else:
        target = s.find('theorem gst_prefix_one_information_bad_descends_inline\n')
        if target < 0:
            raise SystemExit('cannot place bulk source transplant: target theorem absent')
        s = s[:target] + PLACEHOLDER + '\n\n' + s[target:]

# Remove every import whose declaration body is now physically transplanted.
# This also deletes all duplicated import-only packets produced by earlier runs.
lines = []
for line in s.splitlines(keepends=True):
    m = re.match(r'^\s*import\s+([^\s]+)\s*$', line.rstrip('\n'))
    if m and m.group(1) in closure:
        continue
    lines.append(line)
s = ''.join(lines)

# Collapse accidental duplicate surviving header imports (GSTTactic/Mathlib)
# while preserving their first occurrence and all non-import source text.
seen_imports: set[str] = set()
lines = []
for line in s.splitlines(keepends=True):
    m = re.match(r'^\s*import\s+([^\s]+)\s*$', line.rstrip('\n'))
    if m:
        mod = m.group(1)
        if mod in seen_imports:
            continue
        seen_imports.add(mod)
    lines.append(line)
s = ''.join(lines)

bulk_parts = [BULK_BEGIN, '-- Dependency-ordered physical theorem stack.']
for mod in order:
    body = sanitize_module_source(mod)
    bulk_parts.extend([
        f'-- BEGIN ATTACHED {mod}.lean',
        body.rstrip(),
        f'-- END ATTACHED {mod}.lean',
        '',
    ])
bulk_parts.append(BULK_END)
bulk = '\n'.join(bulk_parts) + '\n'
if PLACEHOLDER not in s:
    raise SystemExit('bulk source transplant placeholder vanished')
s = s.replace(PLACEHOLDER, bulk, 1)

# There must now be exactly one physical copy of every transplanted module.
for mod in order:
    marker = f'-- BEGIN ATTACHED {mod}.lean'
    count = s.count(marker)
    if count != 1:
        raise SystemExit(f'expected one physical copy of {mod}, found {count}')
    if re.search(rf'(?m)^\s*import\s+{re.escape(mod)}\s*$', s):
        raise SystemExit(f'import survived for physically transplanted module: {mod}')

# Recovered Aug-23 whole-theorem body replaces the later residual classifier
# seam.  This edit happens after the source transplant so every theorem it uses
# is already physically above it in ErdosTernary2.lean.
start_marker = 'theorem gst_prefix_one_information_bad_descends_inline\n'
end_marker = '\n/-- Corrected information-wave closure:'
start = s.find(start_marker)
if start < 0:
    raise SystemExit('production theorem start not found')
end = s.find(end_marker, start)
if end < 0:
    raise SystemExit('production theorem end marker not found')

replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  -- BEGIN SOL56 FINAL INFINITE MONOLITH TRANSPLANT
  -- Recovered Aug-23 whole-theorem body.  The dependency stack used below is
  -- physically embedded above this theorem; this is not an import-only probe.
  let T : Nat := gstNavigationConstant (s+1) n
  let A : Nat := 4^(3^s)
  let z : Nat := gstCanonicalPrefixOffsetS s
  let H : Nat := z + A*T

  have hchildT : GSTNavigationWitness T := by
    simpa [T] using hchild

  have hparent : GSTSeededBadTraceS 1 H := by
    intro j
    have hj := gst_prefix_one_omega_bad_to_u_seeded_badS s n hs hBad j
    simpa [H, T, A, z, gstPrefixOneUPotentialTailS,
      gstCanonicalPrefixOffsetS] using hj

  have hchildGate : ∃ q, GSTSeededHappyS 0 T q := by
    obtain ⟨q, hd, hspace⟩ := hchildT
    have hmod : gstCarry T q % 3 = 0 :=
      gstGoodSpace_carry_mod3_zero T q hspace
    have hlt : gstCarry T q < 4 := by
      simpa [gstCarry, gstAffineMulCarryS] using
        (gst_affine_carry_lt_multiplierS 4 0 T q (by decide) (by decide))
    have hcarry : gstCarry T q = 0 ∨ gstCarry T q = 3 := by
      omega
    refine ⟨q, ?_⟩
    constructor
    · simpa [T, gstDigitS, gstDigit] using hd
    · simpa [T, gstAffineMulCarryS, gstCarry] using hcarry

  have hApos : 0 < A := by
    dsimp [A]
    positivity

  have hAunit :
      A = 1 + 3^(s+1) * gstNavigationConstant s 1 := by
    dsimp [A]
    simpa using (gst_navigation_decomposition s 1 hs)

  have hunitPrefix :
      gstNavigationConstant s 1 = 1 + 3*z := by
    simpa [z] using gst_navigation_constant_unit_prefixS s hs

  have hz1 : 1 + 4*z < A := by
    have hD9 : 9 ≤ 3^(s+1) := by
      rw [show (9:Nat) = 3^2 by decide]
      exact Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    rw [hAunit, hunitPrefix]
    nlinarith

  have htrap : GSTCanonicalRightChordTrapS A z T :=
    gst_canonical_right_chord_trapS A z T hApos hz1 hparent hchildGate

  obtain ⟨q, hgate, hparentSuffix, hchildSuffix, hC,
    hlocal, hclass3, hclass2, hshared, hW⟩ := htrap

  let D : Nat := gstAffineMulCarryS 4 1 (z + A*T) (q+1)
  let Z : Nat := gstAffineMulCarryS A z T (q+1)
  let W : Nat := gstAffineMulCarryS A (1 + 4*z) (4*T) (q+1)
  let C : Nat := gstAffineMulCarryS 4 0 T (q+1)
  let Y : Nat := T / 3^(q+1)

  have hparentSuffix' : GSTSeededBadTraceS D (Z + A*Y) := by
    simpa [D, Z, Y] using hparentSuffix
  have hchildSuffix' : GSTSeededBadTraceS C Y := by
    simpa [C, Y] using hchildSuffix
  have hC' : C = 2 ∨ C = 3 := by
    simpa [C] using hC
  have hshared' : D + 4*Z = W + A*C := by
    simpa [D, Z, W, C] using hshared
  have hW' : W < A := by
    simpa [W] using hW

  have hDlt : D < 4 := by
    dsimp [D]
    exact gst_affine_carry_lt_multiplierS 4 1 (z + A*T) (q+1)
      (by decide) (by decide)

  obtain ⟨a, b, e, Wmid, hDb, hCe, ha, hb, he, hWmid,
      hmid, hlow⟩ :=
    gst_shared_x4_binary_factor_last_gate_high_bitS
      A D Z W C hApos hDlt hC' hW' hshared'

  have hfuture0 : T / 3^T = 0 := by
    simpa [T] using gst_prefix_one_bigN_future_zero_inline s n hs

  -- Exact RED frontier after the physical source transplant.
  trace_state
  contradiction
  -- END SOL56 FINAL INFINITE MONOLITH TRANSPLANT
'''

s2 = s[:start] + replacement + s[end:]

if re.search(r'(?m)^\s*gst_end\s*$', s2):
    raise SystemExit('gst_end survived final theorem transplant')

new_end = s2.find(end_marker, start)
region = s2[start:new_end]
for forbidden in (
    'let r := v3 n',
    'have hboundary : GSTResidualBoundary',
    'have hResidualBad : GSTOmegaInfiniteBadTrace s k m',
    'rcases hboundary with hlevel1 | hlevel3 | hstable',
):
    if forbidden in region:
        raise SystemExit(f'old residual body survived direct transplant: {forbidden}')

MAIN.write_text(s2, encoding='utf-8')

lines = s2.splitlines()
print(f'BULK_TRANSPLANTED_MODULES={len(order)}')
print(f'BULK_TRANSPLANTED_SOURCE_LINES={sum(len(sanitize_module_source(m).splitlines()) for m in order)}')
for i, line in enumerate(lines, 1):
    if BULK_BEGIN in line:
        print(f'BULK_TRANSPLANT_START={i}')
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'TRANSPLANT_TARGET_START={i}')
    if 'Exact RED frontier after the physical source transplant.' in line:
        print(f'TRANSPLANT_RED_FRONTIER={i}')
print('DIRECT_MONOLITH_TRANSPLANT=PHYSICAL_SOURCE_STACK_AND_WHOLE_THEOREM')
