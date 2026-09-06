#!/usr/bin/env python3
"""Repository census for the Problem 406 / GST Lean workspace.

This script is intentionally read-only.  It scans the checked-out repository and
prints machine-readable census blocks for:

* custom Lean source line counts;
* the import closure of ErdosTernary2.lean, excluding external Lean libraries;
* declaration counts, with theorem/lemma declarations split into deterministic
  architecture families.

The family classifier is lexical and path-aware.  It is meant as an audit map,
not as a mathematical proof that every declaration has only one conceptual role.
"""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable

ROOT = Path(__file__).resolve().parents[1]
MAIN_MONOLITH = Path("ErdosTernary2.lean")
EXTERNAL_IMPORT_PREFIXES = (
    "Mathlib",
    "Std",
    "Lean",
    "Init",
)
DECL_RE = re.compile(
    r"^\s*(?:@[\w\[\]\s,._:=()'\"/-]+\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|axiom|opaque|inductive|structure|class|instance)"
    r"\s+(?P<name>[^\s:{(]+)",
)
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")


def strip_lean_comments(src: str) -> str:
    """Remove Lean comments while preserving newlines for stable line locations."""
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
        ch = src[i]
        if depth == 0:
            out.append(ch)
        elif ch == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def lean_files() -> list[Path]:
    files: list[Path] = []
    for path in ROOT.rglob("*.lean"):
        rel = path.relative_to(ROOT)
        if any(part.startswith(".") and part != ".github" for part in rel.parts):
            continue
        if ".lake" in rel.parts:
            continue
        files.append(rel)
    return sorted(files, key=lambda p: str(p))


def line_count(path: Path) -> int:
    text = (ROOT / path).read_text(encoding="utf-8")
    if text == "":
        return 0
    return text.count("\n") + (0 if text.endswith("\n") else 1)


def module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def direct_imports(path: Path) -> list[str]:
    text = (ROOT / path).read_text(encoding="utf-8")
    modules: list[str] = []
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            modules.append(m.group(1))
    return modules


def custom_import_closure(start: Path) -> list[Path]:
    seen: set[Path] = set()
    stack = [start]
    while stack:
        path = stack.pop()
        if path in seen:
            continue
        if not (ROOT / path).exists():
            continue
        seen.add(path)
        for mod in direct_imports(path):
            if mod.startswith(EXTERNAL_IMPORT_PREFIXES):
                continue
            imp_path = module_to_path(mod)
            if (ROOT / imp_path).exists() and imp_path not in seen:
                stack.append(imp_path)
    return sorted(seen, key=lambda p: str(p))


def declarations(paths: Iterable[Path]) -> list[dict[str, object]]:
    decls: list[dict[str, object]] = []
    for rel in paths:
        src = (ROOT / rel).read_text(encoding="utf-8")
        clean = strip_lean_comments(src)
        for idx, line in enumerate(clean.splitlines(), start=1):
            m = DECL_RE.match(line)
            if not m:
                continue
            decls.append(
                {
                    "path": str(rel),
                    "line": idx,
                    "kind": m.group("kind"),
                    "name": m.group("name"),
                    "family": family_for(str(rel), m.group("name"), m.group("kind")),
                }
            )
    return decls


def has_any(haystack: str, needles: Iterable[str]) -> bool:
    h = haystack.lower()
    return any(n in h for n in needles)


def family_for(path: str, name: str, kind: str) -> str:
    p = path.lower()
    n = name.lower()
    joined = f"{p} {n}"

    if has_any(joined, ["erdos", "problem406", "contains_two_digit", "universal"]):
        return "Final Problem406 theorem layer"
    if has_any(joined, ["exponent", "trit", "prefixlaw", "prefix_law", "prefix_trit", "obstruction"]):
        return "Exponent-prefix / trit obstruction engine"
    if has_any(joined, ["common_two", "commontwo", "fourpower", "four_power", "pow4", "power4", "pure_power", "mod9", "residue", "residual"]):
        return "Four-power / common-two arithmetic engine"
    if has_any(joined, ["canonical", "collision", "terminal", "escape", "phase", "wave", "transparent", "u2d", "crossing"]):
        return "Canonical tail / collision / wave engine"
    if has_any(joined, ["carry", "affine", "coordinate", "quotient", "tail_div", "slice", "information", "state_exact", "mulcarry"]):
        return "Carry / affine information-state engine"
    if has_any(joined, ["digit", "ternary", "noternarytwo", "base3", "pow2", "pow_two", "mod3"]):
        return "Ternary digit arithmetic engine"
    if has_any(joined, ["certificate", "provider", "master", "bridge", "adapter", "realization", "witness"]):
        return "Certificate / provider / bridge layer"
    if has_any(joined, ["tactic", "macro", "elab", "syntax"]):
        return "Custom tactic / automation layer"
    if has_any(joined, ["audit", "axiomreport", "surfacecheck", "manifest"]):
        return "Audit / public-surface tooling"
    if has_any(joined, ["gst", "graph", "navigation", "happycell", "happy", "world", "ontological", "space"]):
        return "General Space Theory proper"
    return "Other support lemmas"


def summarize(label: str, paths: list[Path]) -> dict[str, object]:
    decls = declarations(paths)
    kind_counts = Counter(d["kind"] for d in decls)
    theorem_like = [d for d in decls if d["kind"] in {"theorem", "lemma"}]
    family_counts = Counter(d["family"] for d in theorem_like)
    lines_by_file = {str(p): line_count(p) for p in paths}
    lines_by_top = Counter()
    for p, n in lines_by_file.items():
        top = p.split("/", 1)[0]
        lines_by_top[top] += n
    return {
        "label": label,
        "file_count": len(paths),
        "total_lines": sum(lines_by_file.values()),
        "lines_by_top_level": dict(sorted(lines_by_top.items())),
        "declaration_count": len(decls),
        "declaration_kinds": dict(sorted(kind_counts.items())),
        "theorem_like_count": len(theorem_like),
        "theorem_like_families": dict(sorted(family_counts.items())),
        "largest_files_by_lines": sorted(
            lines_by_file.items(), key=lambda kv: (-kv[1], kv[0])
        )[:30],
    }


def main() -> None:
    all_lean = lean_files()
    closure = custom_import_closure(MAIN_MONOLITH)
    tactic_files = [p for p in all_lean if "tactic" in str(p).lower()]
    closure_plus_tactics = sorted(set(closure) | set(tactic_files), key=lambda p: str(p))

    report = {
        "head_note": "Run inside checked-out GitHub Actions workspace.",
        "main_monolith": str(MAIN_MONOLITH),
        "monolith_lines": line_count(MAIN_MONOLITH),
        "monolith_direct_custom_imports": [
            m for m in direct_imports(MAIN_MONOLITH) if not m.startswith(EXTERNAL_IMPORT_PREFIXES)
        ],
        "monolith_direct_external_imports": [
            m for m in direct_imports(MAIN_MONOLITH) if m.startswith(EXTERNAL_IMPORT_PREFIXES)
        ],
        "all_custom_lean_source": summarize("all custom Lean source files", all_lean),
        "monolith_custom_import_closure": summarize("ErdosTernary2 custom import closure", closure),
        "monolith_closure_plus_all_tactics": summarize(
            "ErdosTernary2 closure plus all tactic files", closure_plus_tactics
        ),
    }

    print("PROBLEM406_CENSUS_JSON_BEGIN")
    print(json.dumps(report, indent=2, sort_keys=True))
    print("PROBLEM406_CENSUS_JSON_END")

    # Human-readable executive lines for CI logs.
    all_src = report["all_custom_lean_source"]
    closure_src = report["monolith_custom_import_closure"]
    closure_tactics = report["monolith_closure_plus_all_tactics"]
    print(f"PROBLEM406_ALL_CUSTOM_LEAN_FILES={all_src['file_count']}")
    print(f"PROBLEM406_ALL_CUSTOM_LEAN_LINES={all_src['total_lines']}")
    print(f"PROBLEM406_ALL_CUSTOM_THEOREM_LIKE={all_src['theorem_like_count']}")
    print(f"PROBLEM406_MONOLITH_LINES={report['monolith_lines']}")
    print(f"PROBLEM406_IMPORT_CLOSURE_FILES={closure_src['file_count']}")
    print(f"PROBLEM406_IMPORT_CLOSURE_LINES={closure_src['total_lines']}")
    print(f"PROBLEM406_IMPORT_CLOSURE_THEOREM_LIKE={closure_src['theorem_like_count']}")
    print(f"PROBLEM406_CLOSURE_PLUS_TACTIC_FILES={closure_tactics['file_count']}")
    print(f"PROBLEM406_CLOSURE_PLUS_TACTIC_LINES={closure_tactics['total_lines']}")
    print(f"PROBLEM406_CLOSURE_PLUS_TACTIC_THEOREM_LIKE={closure_tactics['theorem_like_count']}")


if __name__ == "__main__":
    main()
