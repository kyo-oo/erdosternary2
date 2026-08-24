#!/usr/bin/env python3
from pathlib import Path
import re

MONOLITH = Path('ErdosTernary2.lean')
SNAPSHOT_ROOT = Path(
    'ker07-snapshot/branches/16_sol_latest__5c579-final-bigN-right-chord-atomic'
)
MIN_MONOLITH_BYTES = 300_000
PRESERVE_IMPORTS = {'GSTTactic'}
TARGET = 'theorem gst_prefix_one_information_bad_descends_inline\n'
TARGET_END = '\n/-- Corrected information-wave closure:'

s = MONOLITH.read_text(encoding='utf-8')
original_bytes = len(s.encode('utf-8'))
if original_bytes < MIN_MONOLITH_BYTES:
    raise SystemExit(
        f'refusing transplant into truncated ErdosTernary2.lean: {original_bytes} bytes'
    )

# Concurrent historical surgery runs may have attached the same source packet
# more than once. Normalize the physical monolith first: exactly one packet per
# source filename, preserving the first complete body and deleting later copies.
packet_re = re.compile(
    r'(?ms)^-- BEGIN ATTACHED (?P<name>[^\n]+\.lean)\s*\n'
    r'.*?^-- END ATTACHED (?P=name)\s*\n?'
)
packet_names_seen = set()
duplicate_packets_removed = []

def dedupe_packet(match):
    name = match.group('name')
    if name in packet_names_seen:
        duplicate_packets_removed.append(name)
        return ''
    packet_names_seen.add(name)
    return match.group(0)

s = packet_re.sub(dedupe_packet, s)


def source_path(mod: str):
    if mod in PRESERVE_IMPORTS or mod == 'ErdosTernary2':
        return None
    rel = Path(*mod.split('.')).with_suffix('.lean')
    if rel.exists() and rel != MONOLITH:
        return rel
    snap = SNAPSHOT_ROOT / rel.name
    if snap.exists():
        return snap
    return None


def imports_of(text: str):
    return re.findall(r'(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*$', text)


def strip_imports(text: str):
    return re.sub(r'(?m)^\s*import\s+[A-Za-z0-9_.]+\s*\n?', '', text)


def packet_begin(path: Path):
    return f'-- BEGIN ATTACHED {path.name}'


def packet_end(path: Path):
    return f'-- END ATTACHED {path.name}'


existing_packet_names = set(
    re.findall(r'(?m)^-- BEGIN ATTACHED ([^\n]+\.lean)\s*$', s)
)

# Every local import becomes literal source in the monolith. Repeated imports
# collapse to one dependency root and dependencies are topologically ordered.
root_modules = []
for mod in imports_of(s):
    if source_path(mod) is not None and mod not in root_modules:
        root_modules.append(mod)

order = []
seen = set()
active = set()


def visit(mod: str):
    if mod in seen or mod in PRESERVE_IMPORTS or mod == 'ErdosTernary2':
        return
    path = source_path(mod)
    if path is None:
        return
    if mod in active:
        raise SystemExit(f'local import cycle while packing monolith: {mod}')
    active.add(mod)
    text = path.read_text(encoding='utf-8')
    for dep in imports_of(text):
        if dep == 'ErdosTernary2':
            continue
        if source_path(dep) is not None:
            visit(dep)
    active.remove(mod)
    seen.add(mod)
    order.append((mod, path))


for root in root_modules:
    visit(root)


def remove_local_import(match):
    mod = match.group(1)
    if source_path(mod) is not None:
        return ''
    return match.group(0)

s = re.sub(
    r'(?m)^\s*import\s+([A-Za-z0-9_.]+)\s*\n?',
    remove_local_import,
    s,
)

# Attach only bodies not already in the physical monolith. All source-level
# imports are stripped because their dependency bodies are in this same file.
packets = []
new_packet_names = []
for mod, path in order:
    if path.name in existing_packet_names:
        continue
    body = strip_imports(path.read_text(encoding='utf-8')).strip()
    if not body:
        raise SystemExit(f'empty local theorem source: {path}')
    packets.append(
        f'\n\n{packet_begin(path)}\n'
        f'{body}\n'
        f'{packet_end(path)}\n'
    )
    new_packet_names.append(path.name)
    existing_packet_names.add(path.name)

if s.count(TARGET) != 1:
    raise SystemExit(f'expected exactly one production theorem start, found {s.count(TARGET)}')
insert_at = s.index(TARGET)
if packets:
    s = s[:insert_at] + ''.join(packets) + '\n' + s[insert_at:]

if s.count(TARGET) != 1:
    raise SystemExit('production theorem multiplicity changed during source absorption')
start = s.index(TARGET)
end = s.find(TARGET_END, start)
if end < 0:
    raise SystemExit('production theorem end marker not found')

replacement = r'''theorem gst_prefix_one_information_bad_descends_inline
    (s n : Nat) (hs : 1 ≤ s) (hn : 1 ≤ n)
    (hBad : GSTOmegaInfiniteBadTrace s 1 n) :
    GSTCompleteBadTrace (gstNavigationConstant (s+1) n) := by
  apply gst_complete_bad_of_no_navigation
  intro hchild

  -- BEGIN SOL56 FINAL INFINITE MONOLITH TRANSPLANT
  -- Recovered Aug-23 whole-theorem body.  All local theorem dependencies above
  -- are now literal source in this same ErdosTernary2.lean file.
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

  -- Exact recovered RED frontier.  The next edit is the final consumer only;
  -- all dependency modules have been physically transplanted above.
  trace_state
  contradiction
  -- END SOL56 FINAL INFINITE MONOLITH TRANSPLANT
'''

s2 = s[:start] + replacement + s[end:]

if re.search(r'(?m)^\s*gst_end\s*$', s2):
    raise SystemExit('gst_end survived final theorem transplant')

region_end = s2.find(TARGET_END, start)
region = s2[start:region_end]
for forbidden in (
    'let r := v3 n',
    'have hboundary : GSTResidualBoundary',
    'have hResidualBad : GSTOmegaInfiniteBadTrace s k m',
    'rcases hboundary with hlevel1 | hlevel3 | hstable',
):
    if forbidden in region:
        raise SystemExit(f'old residual body survived direct transplant: {forbidden}')

remaining_local_imports = [
    mod for mod in imports_of(s2) if source_path(mod) is not None
]
if remaining_local_imports:
    raise SystemExit(f'local imports survived physical transplant: {remaining_local_imports}')

# Final physical-packet multiplicity audit: no attached module may occur twice.
final_packet_names = re.findall(
    r'(?m)^-- BEGIN ATTACHED ([^\n]+\.lean)\s*$', s2
)
if len(final_packet_names) != len(set(final_packet_names)):
    dupes = sorted({n for n in final_packet_names if final_packet_names.count(n) > 1})
    raise SystemExit(f'duplicate source packets survived normalization: {dupes}')

final_bytes = len(s2.encode('utf-8'))
if final_bytes < MIN_MONOLITH_BYTES:
    raise SystemExit(f'refusing to write truncated monolith: {final_bytes} bytes')
if s2.count(TARGET) != 1:
    raise SystemExit('post-transplant theorem multiplicity check failed')

MONOLITH.write_text(s2, encoding='utf-8')
written = MONOLITH.read_text(encoding='utf-8')
if written != s2 or len(written.encode('utf-8')) < MIN_MONOLITH_BYTES:
    raise SystemExit('post-write monolith integrity check failed')

print(f'DIRECT_MONOLITH_INPUT_BYTES={original_bytes}')
print(f'DIRECT_MONOLITH_OUTPUT_BYTES={len(written.encode("utf-8"))}')
print(f'DUPLICATE_PACKETS_REMOVED={len(duplicate_packets_removed)}')
for name in duplicate_packets_removed:
    print(f'REMOVED_DUPLICATE_SOURCE={name}')
print(f'LOCAL_IMPORT_ROOTS={len(root_modules)}')
print(f'LOCAL_DEPENDENCY_CLOSURE={len(order)}')
print(f'NEW_SOURCE_PACKETS={len(new_packet_names)}')
for name in new_packet_names:
    print(f'ATTACHED_SOURCE={name}')
for i, line in enumerate(written.splitlines(), 1):
    if 'theorem gst_prefix_one_information_bad_descends_inline' in line:
        print(f'TRANSPLANT_TARGET_START={i}')
    if 'Exact recovered RED frontier.' in line:
        print(f'TRANSPLANT_RED_FRONTIER={i}')
print('DIRECT_MONOLITH_TRANSPLANT=DEDUPED_LOCAL_DEPENDENCY_CLOSURE')
