#!/usr/bin/env python3
"""Compatibility entrypoint for the professional public-surface pass."""
from __future__ import annotations

from pathlib import Path

from professional_surface_apply import HEADER, main as apply_main


ROOT = Path.cwd()

ALIAS_REPLACEMENTS = {
    "theorem adjacent_bad_trace_of_no_navigation :=\n  gst_twoWave_badTrace_of_no_navigation":
        "theorem adjacent_bad_trace_of_no_navigation :\n    _ := by\n  exact gst_twoWave_badTrace_of_no_navigation",
    "theorem large_adjacent_four_power_wave :=\n  gst_power_two_wave_large":
        "theorem large_adjacent_four_power_wave :\n    _ := by\n  exact gst_power_two_wave_large",
    "theorem prefix_one_navigation_lift_of_creation_master :=\n  gst_prefix_one_navigation_lift_of_master_inline":
        "theorem prefix_one_navigation_lift_of_creation_master :\n    _ := by\n  exact gst_prefix_one_navigation_lift_of_master_inline",
    "theorem terminal_step_six_packet :=\n  gst_step6_terminal_packet_kernel":
        "theorem terminal_step_six_packet :\n    _ := by\n  exact gst_step6_terminal_packet_kernel",
    "theorem second_micro_output_eq_x4_output :=\n  gst_second_micro_output_eq_x4_outputS":
        "theorem second_micro_output_eq_x4_output :\n    _ := by\n  exact gst_second_micro_output_eq_x4_outputS",
    "theorem physical_two_digit_chord_forces_plus :=\n  gst_physical_two_digit_chord_forces_gst_plusS":
        "theorem physical_two_digit_chord_forces_plus :\n    _ := by\n  exact gst_physical_two_digit_chord_forces_gst_plusS",
    "theorem physical_two_digit_chord_event_word :=\n  gst_physical_two_digit_chord_event_88S":
        "theorem physical_two_digit_chord_event_word :\n    _ := by\n  exact gst_physical_two_digit_chord_event_88S",
    "theorem physical_two_digit_chord_code :=\n  gst_physical_two_digit_chord_35S":
        "theorem physical_two_digit_chord_code :\n    _ := by\n  exact gst_physical_two_digit_chord_35S",
    "theorem happy_digit_two_clear_iff_plus :=\n  gst_happy_big2_two_digit_clear_iff_plusS":
        "theorem happy_digit_two_clear_iff_plus :\n    _ := by\n  exact gst_happy_big2_two_digit_clear_iff_plusS",
    "theorem happy_digit_two_not_clear_is_null :=\n  gst_happy_big2_two_digit_not_clear_is_nullS":
        "theorem happy_digit_two_not_clear_is_null :\n    _ := by\n  exact gst_happy_big2_two_digit_not_clear_is_nullS",
    "theorem happy_digit_two_right_chord_dichotomy :=\n  gst_happy_big2_right_chord_dichotomyS":
        "theorem happy_digit_two_right_chord_dichotomy :\n    _ := by\n  exact gst_happy_big2_right_chord_dichotomyS",
    "theorem last_child_gate_right_chord :=\n  gst_last_child_gate_right_chordS":
        "theorem last_child_gate_right_chord :\n    _ := by\n  exact gst_last_child_gate_right_chordS",
    "theorem navigation_witness_of_canonical_navigation :=\n  gst_navigation_witness_of_standalone_navigation":
        "theorem navigation_witness_of_canonical_navigation :\n    _ := by\n  exact gst_navigation_witness_of_standalone_navigation",
    "theorem bigN_seed_three_endpoint_forces_non_one :=\n  gst_bigN_seed3_endpoint_forces_non_one_inline":
        "theorem bigN_seed_three_endpoint_forces_non_one :\n    _ := by\n  exact gst_bigN_seed3_endpoint_forces_non_one_inline",
    "theorem prefix_one_bigN_future_zero :=\n  gst_prefix_one_bigN_future_zero_inline":
        "theorem prefix_one_bigN_future_zero :\n    _ := by\n  exact gst_prefix_one_bigN_future_zero_inline",
}

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
    for old, new in ALIAS_REPLACEMENTS.items():
        text = text.replace(old, new)
    path.write_text(text, encoding="utf-8")


def main() -> None:
    apply_main()
    normalize_monolith_header(ROOT / "ErdosTernary2.lean")
    normalize_monolith_header(ROOT / "FINISHER" / "ErdosTernary2.lean")
    for rel in ALIAS_FILES:
        fix_wrapper_aliases(ROOT / rel)


if __name__ == "__main__":
    main()
