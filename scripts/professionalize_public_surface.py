#!/usr/bin/env python3
"""Compatibility entrypoint for the professional public-surface pass."""
from __future__ import annotations

from pathlib import Path

from professional_surface_apply import HEADER, main as apply_main


ROOT = Path.cwd()

ALIAS_PAIRS = [
    ("adjacent_bad_trace_of_no_navigation", "gst_twoWave_badTrace_of_no_navigation"),
    ("large_adjacent_four_power_wave", "gst_power_two_wave_large"),
    ("prefix_one_navigation_lift_of_creation_master", "gst_prefix_one_navigation_lift_of_master_inline"),
    ("terminal_step_six_packet", "gst_step6_terminal_packet_kernel"),
    ("second_micro_output_eq_x4_output", "gst_second_micro_output_eq_x4_outputS"),
    ("physical_two_digit_chord_forces_plus", "gst_physical_two_digit_chord_forces_gst_plusS"),
    ("physical_two_digit_chord_event_word", "gst_physical_two_digit_chord_event_88S"),
    ("physical_two_digit_chord_code", "gst_physical_two_digit_chord_35S"),
    ("happy_digit_two_clear_iff_plus", "gst_happy_big2_two_digit_clear_iff_plusS"),
    ("happy_digit_two_not_clear_is_null", "gst_happy_big2_two_digit_not_clear_is_nullS"),
    ("happy_digit_two_right_chord_dichotomy", "gst_happy_big2_right_chord_dichotomyS"),
    ("last_child_gate_right_chord", "gst_last_child_gate_right_chordS"),
    ("navigation_witness_of_canonical_navigation", "gst_navigation_witness_of_standalone_navigation"),
    ("bigN_seed_three_endpoint_forces_non_one", "gst_bigN_seed3_endpoint_forces_non_one_inline"),
    ("prefix_one_bigN_future_zero", "gst_prefix_one_bigN_future_zero_inline"),
]

ALIAS_FILES = [
    "GST/Problem406/FourPower.lean",
    "GST/Problem406/PrefixOne.lean",
    "GST/Problem406/LocalCell.lean",
    "GST/Problem406/Navigation.lean",
    "FINISHER/GST/Problem406/FourPower.lean",
    "FINISHER/GST/Problem406/PrefixOne.lean",
    "FINISHER/GST/Problem406/LocalCell.lean",
    "FINISHER/GST/Problem406/Navigation.lean",
]


def normalize_monolith_header(path: Path) -> None:
    if not path.exists():
        return
    lines = path.read_text(encoding="utf-8").splitlines()
    import_start = next((i for i, line in enumerate(lines) if line.startswith("import ")), None)
    if import_start is None:
        raise RuntimeError(f"No import block found in {path}")
    import_end = import_start
    while import_end < len(lines) and lines[import_end].startswith("import "):
        import_end += 1
    import_block = "\n".join(lines[import_start:import_end])
    rest = "\n".join(lines[import_end:]).lstrip("\n")
    while rest.startswith(HEADER):
        rest = rest[len(HEADER):].lstrip("\n")
    path.write_text(f"{import_block}\n\n{HEADER}\n\n{rest.rstrip()}\n", encoding="utf-8")


def fix_wrapper_aliases(path: Path) -> None:
    if not path.exists():
        return
    text = path.read_text(encoding="utf-8")
    for name, target in ALIAS_PAIRS:
        abbrev = f"abbrev {name} :=\n  {target}"
        text = text.replace(f"theorem {name} :=\n  {target}", abbrev)
        text = text.replace(f"theorem {name} :\n    _ := by\n  exact {target}", abbrev)
    path.write_text(text, encoding="utf-8")


def main() -> None:
    apply_main()
    normalize_monolith_header(ROOT / "ErdosTernary2.lean")
    normalize_monolith_header(ROOT / "FINISHER" / "ErdosTernary2.lean")
    for rel in ALIAS_FILES:
        fix_wrapper_aliases(ROOT / rel)


if __name__ == "__main__":
    main()
