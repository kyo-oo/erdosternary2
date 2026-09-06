#!/usr/bin/env python3
"""Apply the professional Problem 406 public-surface pass."""
from __future__ import annotations

import hashlib
import re
import shutil
from pathlib import Path

ROOT = Path.cwd()
BANNED_TERMS = ["GPT", "ChatGPT", "OpenAI", "Claude", "SOL56", "younger-Sol", "Old Sol", "Boss", "🌟"]
DECL_RE = re.compile(
    r"^\s*(?:@[\w\[\]\s,._:=()'\"/-]+\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|axiom|opaque|inductive|structure|class|instance)"
    r"\s+(?P<name>[^\s:{(]+)", re.MULTILINE)

HEADER = """/-!
# Erdős ternary-2 theorem

This file contains the monolithic Lean proof object for the ternary digit-two
theorem: for every exponent `n ≥ 9`, the ternary expansion of `2^n` contains
the digit `2`.

The file is intentionally kept as a single checked proof artifact.  Public,
reviewer-facing names are provided in the `GST.Problem406.*` API modules.  The
statements below remain the internal proof spine used by those wrappers.

## Main declarations

* `erdos_ternary_2_universal`: final theorem for powers of two.
* `erdos_ternary_2_even_universal`: even-exponent reduction through powers of four.
* `gst_power_two_wave_large`: large adjacent-four-power wave theorem.
* `gst_prefix_one_navigation_lift`: prefix-one navigation bridge.
* `gst_four_power_creation_master_inline`: creation master used by the bridge.

## Presentation discipline

Comments in this file describe mathematical interfaces, proof reductions, and
local finite classifications.  Personal handoff notes, tool references, and
chronological scratch labels are excluded from the public presentation layer.
-/"""

CANONICAL = """-- Canonical pure-power/information transplant layer: the following declarations
-- connect the finite residue machinery to the prefix-one navigation interface.
"""

FILES: dict[str, str] = {
"GST/Problem406/Core.lean": """import ErdosTernary2

/-!
# Core Problem 406 API

Stable public names for the final ternary digit-two theorem.  This module wraps
the checked monolith without changing proof bodies.
-/

namespace GST
namespace Problem406

/-- Boolean predicate: the ternary expansion contains a digit `2`. -/
abbrev containsDigitTwo : Nat → Bool := hasTernaryTwo

/-- Boolean predicate: the ternary expansion contains no digit `2`. -/
abbrev containsNoDigitTwo : Nat → Bool := noTernaryTwo

/-- Main public theorem: every `2^n` with `n ≥ 9` has a ternary digit `2`. -/
theorem power_of_two_contains_digit_two
    (n : Nat) (hn : 9 ≤ n) :
    containsNoDigitTwo (2^n) = false := by
  exact erdos_ternary_2_universal n hn

end Problem406
end GST
""",
"GST/Problem406/FourPower.lean": """import ErdosTernary2

/-!
# Four-power reduction API

Public names for the even-exponent and adjacent-wave layer of the Problem 406
proof.
-/

namespace GST
namespace Problem406

/-- The assertion that `4^a` has ternary digit `2`. -/
abbrev FourPowerHasDigitTwo (a : Nat) : Prop := hasTernaryTwo (4^a) = true

/-- Two adjacent four-power waves overlap through the navigation alternative. -/
abbrev AdjacentFourPowerWave : Nat → Prop := GSTPowerTwoWave

/-- Complete two-wave bad trace for adjacent multiplication by four. -/
abbrev AdjacentFourPowerBadTrace : Nat → Prop := GSTTwoWaveBadTrace

/-- Exact adjacent-power identity used by the even-exponent reduction. -/
theorem adjacent_four_power_identity
    (a : Nat) (ha : 1 ≤ a) :
    4 * 4^(a-1) = 4^a := by
  exact gst_four_pow_adjacent a ha

/-- Failure of both navigation alternatives gives a complete two-wave bad trace. -/
theorem adjacent_bad_trace_of_no_navigation :=
  gst_twoWave_badTrace_of_no_navigation

/-- Large adjacent four-power waves satisfy the navigation alternative. -/
theorem large_adjacent_four_power_wave :=
  gst_power_two_wave_large

/-- Every `4^a` with `a ≥ 5` has ternary digit `2`. -/
theorem four_power_contains_digit_two
    (a : Nat) (ha : 5 ≤ a) :
    FourPowerHasDigitTwo a := by
  exact erdos_ternary_2_even_universal a ha

end Problem406
end GST
""",
"GST/Problem406/PrefixOne.lean": """import ErdosTernary2

/-!
# Prefix-one bridge API

Public names for the bridge carrying four-power creation certificates into the
prefix-one navigation layer.
-/

namespace GST
namespace Problem406

/-- Public name for the prefix-one navigation lifting proposition. -/
abbrev PrefixOneNavigationLift : Prop := GSTPrefixOneNavigationLift

/-- Public name for the four-power creation master proposition. -/
abbrev FourPowerCreationMaster : Prop := GSTFourPowerOntologicalAdapter.FourPowerCreationMaster

/-- The four-power creation master certified inside the monolith. -/
theorem four_power_creation_master : FourPowerCreationMaster := by
  exact gst_four_power_creation_master_inline

/-- A creation master supplies the prefix-one navigation lift. -/
theorem prefix_one_navigation_lift_of_creation_master :=
  gst_prefix_one_navigation_lift_of_master_inline

/-- Certified public prefix-one navigation lift. -/
theorem prefix_one_navigation_lift : PrefixOneNavigationLift := by
  exact gst_prefix_one_navigation_lift

/-- Terminal Step-6 packet exported under a neutral reviewer-facing name. -/
theorem terminal_step_six_packet :=
  gst_step6_terminal_packet_kernel

end Problem406
end GST
""",
"GST/Problem406/LocalCell.lean": """import ErdosTernary2

/-!
# Local cell classification API

Public names for the finite local classification used by the right-chord and
last-gate arguments.
-/

namespace GST
namespace Problem406

/-- Local BIG1-clear condition at one physical digit-two cell. -/
abbrev PhysicalTwoDigitClear : Nat → Nat → Prop := GSTPhysicalTwoDigitBig1ClearS

/-- The second microscopic output equals the ordinary x4 output digit. -/
theorem second_micro_output_eq_x4_output :=
  gst_second_micro_output_eq_x4_outputS

/-- The local clear branch forces the positive carry-three orientation. -/
theorem physical_two_digit_chord_forces_plus :=
  gst_physical_two_digit_chord_forces_gst_plusS

/-- Event-word form of the positive local chord. -/
theorem physical_two_digit_chord_event_word :=
  gst_physical_two_digit_chord_event_88S

/-- Numeric form of the local chord: the aligned two-layer code is `6^2 - 1`. -/
theorem physical_two_digit_chord_code :=
  gst_physical_two_digit_chord_35S

/-- At an already-Happy digit-two cell, clear is equivalent to carry three. -/
theorem happy_digit_two_clear_iff_plus :=
  gst_happy_big2_two_digit_clear_iff_plusS

/-- The complementary branch is the null local orientation. -/
theorem happy_digit_two_not_clear_is_null :=
  gst_happy_big2_two_digit_not_clear_is_nullS

/-- Complete two-branch local dichotomy for a Happy digit-two cell. -/
theorem happy_digit_two_right_chord_dichotomy :=
  gst_happy_big2_right_chord_dichotomyS

/-- Exact local hand-off at the last child Happy gate. -/
theorem last_child_gate_right_chord :=
  gst_last_child_gate_right_chordS

end Problem406
end GST
""",
"GST/Problem406/Navigation.lean": """import ErdosTernary2

/-!
# Navigation API

Public names for the monolith's navigation witness and finite endpoint bridge.
-/

namespace GST
namespace Problem406

/-- Public name for the monolith navigation witness. -/
abbrev NavigationWitness : Nat → Prop := GSTNavigationWitness

/-- Canonical standalone navigation gives the monolith navigation witness. -/
theorem navigation_witness_of_canonical_navigation :=
  gst_navigation_witness_of_standalone_navigation

/-- Finite endpoint adapter for the BIG-N seed-three branch. -/
theorem bigN_seed_three_endpoint_forces_non_one :=
  gst_bigN_seed3_endpoint_forces_non_one_inline

/-- Finite-support horizon for the canonical child information. -/
theorem prefix_one_bigN_future_zero :=
  gst_prefix_one_bigN_future_zero_inline

end Problem406
end GST
""",
"GST/Problem406/PublicAPI.lean": """import GST.Problem406.Core
import GST.Problem406.FourPower
import GST.Problem406.PrefixOne
import GST.Problem406.LocalCell
import GST.Problem406.Navigation

/-!
# Public API for Problem 406

Reviewer-facing namespace for the formalized ternary digit-two theorem.

This file intentionally exposes clean names while preserving the internal
monolithic proof artifact.  The old internal identifiers remain available for
compatibility, but new documentation should cite the names under
`GST.Problem406`.
-/

namespace GST
namespace Problem406

/-- Compatibility name: every exponent `n ≥ 9` gives a ternary digit `2` in `2^n`. -/
theorem contains_two_digit_of_nine_le
    (n : Nat) (hn : 9 ≤ n) :
    containsNoDigitTwo (2^n) = false := by
  exact power_of_two_contains_digit_two n hn

end Problem406
end GST
""",
"GST/Problem406/TheoremMap.lean": """import GST.Problem406.PublicAPI

/-!
# Problem 406 theorem map

Compile-checked index of the reviewer-facing theorem surface.
-/

#check GST.Problem406.power_of_two_contains_digit_two
#check GST.Problem406.contains_two_digit_of_nine_le
#check GST.Problem406.four_power_contains_digit_two
#check GST.Problem406.adjacent_four_power_identity
#check GST.Problem406.adjacent_bad_trace_of_no_navigation
#check GST.Problem406.large_adjacent_four_power_wave
#check GST.Problem406.four_power_creation_master
#check GST.Problem406.prefix_one_navigation_lift_of_creation_master
#check GST.Problem406.prefix_one_navigation_lift
#check GST.Problem406.terminal_step_six_packet
#check GST.Problem406.second_micro_output_eq_x4_output
#check GST.Problem406.physical_two_digit_chord_forces_plus
#check GST.Problem406.physical_two_digit_chord_event_word
#check GST.Problem406.physical_two_digit_chord_code
#check GST.Problem406.happy_digit_two_clear_iff_plus
#check GST.Problem406.happy_digit_two_not_clear_is_null
#check GST.Problem406.happy_digit_two_right_chord_dichotomy
#check GST.Problem406.last_child_gate_right_chord
#check GST.Problem406.navigation_witness_of_canonical_navigation
#check GST.Problem406.bigN_seed_three_endpoint_forces_non_one
#check GST.Problem406.prefix_one_bigN_future_zero

#check erdos_ternary_2_universal
#check erdos_ternary_2_even_universal
#check gst_power_two_wave_large
#check gst_prefix_one_navigation_lift
#check noTernaryTwo
#check hasTernaryTwo
""",
"GST/Audit/PublicSurfaceCheck.lean": """import GST.PublicAPI

/-!
# Public surface smoke check

Compile-checks the clean reviewer-facing public names.  This module contains no
proof bodies.
-/

#check GST.Problem406.power_of_two_contains_digit_two
#check GST.Problem406.contains_two_digit_of_nine_le
#check GST.Problem406.four_power_contains_digit_two
#check GST.Problem406.adjacent_four_power_identity
#check GST.Problem406.large_adjacent_four_power_wave
#check GST.Problem406.four_power_creation_master
#check GST.Problem406.prefix_one_navigation_lift
#check GST.Problem406.terminal_step_six_packet
#check GST.Problem406.happy_digit_two_right_chord_dichotomy
#check GST.Problem406.last_child_gate_right_chord
#check GST.Problem406.navigation_witness_of_canonical_navigation
#check GST.Arithmetic.digit3
#check GST.Arithmetic.Navigation
#check GST.Arithmetic.carry4
#check GST.Arithmetic.carry4_lt_four
#check GST.Arithmetic.carry4_forward_exact
#check GST.FourPower.CommonTwo
#check GST.FourPower.DirectExistence
#check GST.FourPower.exponentPrefix
#check GST.FourPower.exponentTrit
#check GST.FourPower.exponent_prefix_trit_decomposition
#check GST.FourPower.CreationCertificate
#check GST.FourPower.CreationMaster
#check GST.FourPower.creation_certificate_to_navigation
""",
"GST/PublicAPI.lean": """import GST.Problem406.PublicAPI
import GST.Arithmetic.TernaryDigits
import GST.Arithmetic.Carries
import GST.FourPower.CommonTwo
import GST.FourPower.PrefixLaw
import GST.FourPower.Certificate

/-!
# GST public API

Reviewer-facing imports for the Problem 406 formalization.

This umbrella module exposes clean public namespaces while preserving the proof
artifact and internal modules.  The theorem universe is indexed separately; this
API promotes only the mathematical spine and stable bridge statements.
-/
""",
"docs/problem406/public-api-expansion.md": """# Problem 406 public API expansion

This pass expands the reviewer-facing theorem surface without renaming the
internal monolith declarations.

## Policy

The proof corpus contains many internal declarations whose names encode their
construction history.  Renaming all of them in place would be risky and would
create churn through the proof stack.  The professional presentation layer
therefore uses wrappers:

- internal proof identifiers remain stable;
- public names live under `GST.Problem406`;
- the theorem map compile-checks the exposed surface;
- the full theorem universe remains indexed in the FINISHER manifest.

## New public modules

| Module | Purpose |
| --- | --- |
| `GST.Problem406.Core` | final theorem and ternary digit predicates |
| `GST.Problem406.FourPower` | even-exponent/four-power wave layer |
| `GST.Problem406.PrefixOne` | creation-master and prefix-one bridge layer |
| `GST.Problem406.LocalCell` | finite local cell/right-chord classification |
| `GST.Problem406.Navigation` | navigation witness and finite endpoint bridge |

## Style baseline

The public layer follows the same broad style used in mathlib theorem files:
module-level documentation, a small main-declarations surface, local/private
machinery kept internal, and docstrings on promoted declarations.
""",
}


def strip_comments(src: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    while i < len(src):
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            if j == -1:
                break
            out.append("\n")
            i = j + 1
            continue
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        elif src[i] == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def code_fingerprint(src: str) -> str:
    code = re.sub(r"\s+", "", strip_comments(src))
    return hashlib.sha256(code.encode("utf-8")).hexdigest()


def professionalize_monolith(path: Path) -> tuple[int, list[str]]:
    if not path.exists():
        return 0, []
    original = path.read_text(encoding="utf-8")
    before_fp = code_fingerprint(original)
    before_hits = []
    for lineno, line in enumerate(original.splitlines(), 1):
        if any(term in line for term in BANNED_TERMS):
            before_hits.append(f"{path.relative_to(ROOT)}:{lineno}: {line.strip()}")

    lines = original.splitlines()
    import_idx = next((i for i, line in enumerate(lines) if line.startswith("import ")), None)
    if import_idx is None:
        raise RuntimeError(f"No import block found in {path}")
    text = HEADER + "\n\n" + "\n".join(lines[import_idx:]) + "\n"
    text = re.sub(r"(?m)^--\s*SOL56\b.*\n", "", text)
    text = re.sub(r"(?m)^--\s*(BEGIN|END) ATTACHED\b.*\n", "", text)
    text = re.sub(
        r"(?s)(?:-- Full canonical pure-power/information transplant\..*?-- detached probes\.\n\s*)+",
        CANONICAL + "\n",
        text,
    )
    replacements = {
        "Boss's handwritten condition": "The local handwritten condition",
        "Boss's local": "The local",
        "Boss's": "the local",
        "Boss": "the local classifier",
        "younger-Sol's microscopic": "the microscopic",
        "younger-Sol": "the local microscopic layer",
        "Old Sol's information-regeneration": "the information-regeneration",
        "Old Sol": "the earlier information-regeneration layer",
        "SOL56": "presentation",
        "🌟": "",
        "CardinalWorlds_Final.lean": "ErdosTernary2.lean",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    if code_fingerprint(text) != before_fp:
        raise RuntimeError(f"Refusing to rewrite {path}: proof-code fingerprint changed")
    path.write_text(text, encoding="utf-8")
    return len(before_hits), before_hits[:50]


def write(path: str, content: str) -> None:
    target = ROOT / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(content, encoding="utf-8")


def copy_to_finisher(paths: list[str]) -> None:
    if not (ROOT / "FINISHER").exists():
        return
    for rel in paths:
        src = ROOT / rel
        if src.exists():
            dst = ROOT / "FINISHER" / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)


def update_lakefile() -> None:
    path = ROOT / "lakefile.toml"
    text = path.read_text(encoding="utf-8")
    roots = [
        "GST.Problem406.Core",
        "GST.Problem406.FourPower",
        "GST.Problem406.PrefixOne",
        "GST.Problem406.LocalCell",
        "GST.Problem406.Navigation",
    ]
    anchor = '  "GST.Problem406.PublicAPI",\n'
    insert = "".join(f'  "{r}",\n' for r in roots if f'"{r}"' not in text)
    if insert and anchor in text:
        text = text.replace(anchor, insert + anchor)
    path.write_text(text, encoding="utf-8")


def declaration_name_hits() -> list[str]:
    hits: list[str] = []
    terms = ["gpt", "chatgpt", "openai", "claude", "sol56", "boss"]
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        code = strip_comments(path.read_text(encoding="utf-8", errors="ignore"))
        for match in DECL_RE.finditer(code):
            name = match.group("name")
            if any(term in name.lower() for term in terms):
                hits.append(f"{path.relative_to(ROOT)}: {match.group('kind')} {name}")
    return hits


def residual_hits() -> list[str]:
    hits: list[str] = []
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        for lineno, line in enumerate(path.read_text(encoding="utf-8", errors="ignore").splitlines(), 1):
            if any(term in line for term in BANNED_TERMS):
                hits.append(f"{path.relative_to(ROOT)}:{lineno}: {line.strip()}")
    return hits


def write_audit(before_total: int, examples: list[str]) -> None:
    decl = declaration_name_hits()
    resid = residual_hits()
    out: list[str] = []
    out += ["# Presentation hygiene audit", ""]
    out += ["This audit covers Lean source files after the professional surface pass.", ""]
    out += ["## Monolith comment cleanup", ""]
    out += [f"Pre-cleanup personal/tool-era comment hits in the monolith copies: **{before_total}**.", ""]
    if examples:
        out += ["Representative removed or neutralized lines:", ""]
        for hit in examples[:20]:
            out.append(f"- `{hit.replace('`', chr(39))}`")
        out.append("")
    out += ["The script verifies that the comment-stripped, whitespace-normalized Lean proof stream is unchanged before writing each monolith.", ""]
    out += ["## Declaration-name audit", ""]
    if decl:
        out.append("Potential AI/personal references in declaration names remain:")
        out.append("")
        out.extend(f"- `{hit}`" for hit in decl)
    else:
        out.append("No GPT/ChatGPT/OpenAI/Claude/SOL56/Boss tokens were found in Lean declaration names.")
    out += ["", "## Residual Lean-source presentation hits", ""]
    if resid:
        out.append("Residual Lean-source lines requiring future review:")
        out.append("")
        out.extend(f"- `{hit.replace('`', chr(39))}`" for hit in resid[:80])
    else:
        out.append("No banned presentation tokens remain in Lean source files.")
    write("docs/problem406/presentation-hygiene-audit.md", "\n".join(out) + "\n")


def main() -> None:
    before_total = 0
    examples: list[str] = []
    for path in [ROOT / "ErdosTernary2.lean", ROOT / "FINISHER" / "ErdosTernary2.lean"]:
        count, hits = professionalize_monolith(path)
        before_total += count
        examples.extend(hits)
    for path, content in FILES.items():
        write(path, content)
    update_lakefile()
    write_audit(before_total, examples)
    copy_to_finisher(list(FILES) + ["docs/problem406/presentation-hygiene-audit.md"])


if __name__ == "__main__":
    main()
