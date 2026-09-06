#!/usr/bin/env python3
"""Build the FINISHER proof bundle.

The bundle is intentionally generated from two sources:

1. Comparator-final Lean source, pinned at de11dc2c5ee340fee1929ba2adc6834a72ab9879.
2. The current professionalization branch's public API/docs/scripts/CI references.

The original proof source is copied byte-for-byte from the pinned commit into
FINISHER/ using the original module paths.
"""

from __future__ import annotations

import json
import re
import shutil
import subprocess
from collections import Counter
from pathlib import Path

ROOT = Path.cwd()
FINISHER = ROOT / "FINISHER"
TARGET = "de11dc2c5ee340fee1929ba2adc6834a72ab9879"
MAIN = Path("ErdosTernary2.lean")
EXTERNAL = ("Mathlib", "Std", "Lean", "Init")
IMPORT_RE = re.compile(r"^\s*import\s+([A-Za-z0-9_'.]+)\s*$")
DECL_RE = re.compile(
    r"^\s*(?:@[\w\[\]\s,._:=()'\"/-]+\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|axiom|opaque|inductive|structure|class|instance)"
    r"\s+(?P<name>[^\s:{(]+)"
)


def git_bytes(ref: str, path: str) -> bytes:
    return subprocess.check_output(["git", "show", f"{ref}:{path}"])


def git_text(ref: str, path: str) -> str:
    return git_bytes(ref, path).decode("utf-8")


def exists_at(ref: str, path: str) -> bool:
    return subprocess.run(
        ["git", "cat-file", "-e", f"{ref}:{path}"],
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    ).returncode == 0


def write_bytes(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)


def module_to_path(module: str) -> Path:
    return Path(*module.split(".")).with_suffix(".lean")


def imports(ref: str, path: Path) -> list[str]:
    return [
        m.group(1)
        for line in git_text(ref, str(path)).splitlines()
        if (m := IMPORT_RE.match(line))
    ]


def closure(ref: str, start: Path) -> list[Path]:
    seen: set[Path] = set()
    stack = [start]
    while stack:
        path = stack.pop()
        if path in seen or not exists_at(ref, str(path)):
            continue
        seen.add(path)
        for module in imports(ref, path):
            if module.startswith(EXTERNAL):
                continue
            candidate = module_to_path(module)
            if exists_at(ref, str(candidate)) and candidate not in seen:
                stack.append(candidate)
    return sorted(seen, key=str)


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
        ch = src[i]
        if depth == 0:
            out.append(ch)
        elif ch == "\n":
            out.append("\n")
        i += 1
    return "".join(out)


def line_count(text: str) -> int:
    return 0 if text == "" else text.count("\n") + (0 if text.endswith("\n") else 1)


def family(path: str, name: str) -> str:
    x = f"{path} {name}".lower()

    def has(*items: str) -> bool:
        return any(item in x for item in items)

    if has("erdos", "problem406", "universal", "final"):
        return "Final Problem406 / universal theorem layer"
    if has("tdt", "duality", "transcendence"):
        return "True Duality Transcendence layer"
    if has("cascade", "tower", "stable", "bridge", "crossing"):
        return "Bridge / cascade / crossing layer"
    if has("bounded", "modular_depth", "decide", "struct", "verification"):
        return "Finite verification / structural decision layer"
    if has("four", "pow4", "power", "residue", "mod9", "mod27", "mod81"):
        return "Four-power / residue arithmetic layer"
    if has("digit", "ternary", "noternarytwo", "hastwo", "base3"):
        return "Ternary digit arithmetic layer"
    if has("carry", "affine", "information", "coordinate", "quotient"):
        return "Carry / affine information layer"
    if has("canonical", "tail", "collision", "wave", "u2d", "phase", "escape"):
        return "Canonical tail / collision / wave layer"
    if has("tactic", "macro", "elab", "syntax"):
        return "Custom tactic / automation layer"
    if has("gst", "graph", "navigation", "world", "ontological", "space", "happy"):
        return "General Space Theory proper"
    return "Other support theorem layer"


def copy_tree(src: Path, dst: Path) -> list[str]:
    if not src.exists():
        return []
    if dst.exists():
        shutil.rmtree(dst)
    ignore = shutil.ignore_patterns(
        ".git", ".lake", "__pycache__", "*.olean", "*.ilean", "*.trace"
    )
    shutil.copytree(src, dst, ignore=ignore)
    return [str(p.relative_to(FINISHER)) for p in sorted(dst.rglob("*")) if p.is_file()]


def write_reports(lock: dict[str, object], families: Counter[str], line_counts: dict[str, int]) -> None:
    total_lines = int(lock["custom_import_closure_lines"])
    theorem_like = int(lock["custom_import_closure_theorem_like"])
    gst_count = int(lock["general_space_theory_proper_theorem_like"])
    decls = int(lock["custom_import_closure_declarations"])
    kinds = lock["custom_import_closure_declaration_kinds"]
    assert isinstance(kinds, dict)

    fam_rows = "\n".join(
        f"| {name} | {count} |"
        for name, count in sorted(families.items(), key=lambda kv: (-kv[1], kv[0]))
    )
    top_rows = "\n".join(
        f"| `{path}` | {n} |"
        for path, n in sorted(line_counts.items(), key=lambda kv: (-kv[1], kv[0]))[:30]
    )

    (FINISHER / "THEOREM_FAMILIES.md").write_text(
        f"""# FINISHER theorem-family index

Pinned comparator-final source: `{TARGET}`.

This file counts only `ErdosTernary2.lean` plus its recursive custom import closure from the comparator-final source. It excludes Mathlib and excludes later presentation-only files.

## Executive counts

| Item | Count |
| --- | ---: |
| Source files | {lock['custom_import_closure_files']} |
| Source lines | {total_lines} |
| Main monolith lines | {lock['monolith_lines']} |
| Total declarations | {decls} |
| Theorem declarations | {kinds.get('theorem', 0)} |
| Lemma declarations | {kinds.get('lemma', 0)} |
| Theorem-like declarations | {theorem_like} |
| General Space Theory proper theorem-like declarations | {gst_count} |
| Non-GST theorem-like declarations | {theorem_like - gst_count} |

## Theorem families

| Family | Theorem-like declarations |
| --- | ---: |
{fam_rows}

## Largest copied source files

| File | Lines |
| --- | ---: |
{top_rows}

## Public API policy

The full theorem universe is indexed, not mass-aliased. Public API names should promote the proof spine and major bridge layers deliberately, while lower-level declarations stay discoverable through this manifest until they are intentionally promoted.
""",
        encoding="utf-8",
    )

    (FINISHER / "README.md").write_text(
        f"""# FINISHER

`FINISHER/` is the clean final presentation bundle for the Erdős ternary-2 / Problem 406 Lean project.

It freezes the comparator-final proof source and keeps the professional presentation layer beside it.

## Frozen proof source

Pinned source commit:

```text
{TARGET}
```

Main monolith:

```text
FINISHER/ErdosTernary2.lean
```

The recursive custom import closure is copied into this folder using the original module paths.

## Counts

| Item | Count |
| --- | ---: |
| Main monolith lines | {lock['monolith_lines']} |
| Custom import-closure files | {lock['custom_import_closure_files']} |
| Custom import-closure lines | {total_lines} |
| Total declarations | {decls} |
| Theorem-like declarations | {theorem_like} |
| GST-proper theorem-like declarations | {gst_count} |
| Non-GST theorem-like declarations | {theorem_like - gst_count} |

## Important entrypoints

- `ErdosTernary2.lean` — finalized comparator monolith.
- `THEOREM_FAMILIES.md` — theorem-family map.
- `FINISHER.lock.json` — exact machine-readable lock and census.
- `GST/PublicAPI.lean` — curated public API surface.
- `docs/problem406/` and `docs/gst/` — reviewer-facing documentation.

## Decision

Do not mass-wrap all theorem-like declarations. The professional shape is: frozen corpus, full theorem index, then curated public API over the proof spine.
""",
        encoding="utf-8",
    )


def main() -> None:
    subprocess.check_call(["git", "cat-file", "-e", f"{TARGET}^{{commit}}"])
    shutil.rmtree(FINISHER, ignore_errors=True)
    FINISHER.mkdir(parents=True)

    source_files = closure(TARGET, MAIN)
    for rel in source_files:
        write_bytes(FINISHER / rel, git_bytes(TARGET, str(rel)))

    for name in ["lean-toolchain", "lake-manifest.json", "README.md"]:
        if exists_at(TARGET, name):
            write_bytes(FINISHER / name, git_bytes(TARGET, name))
    if (ROOT / "lakefile.toml").exists():
        shutil.copy2(ROOT / "lakefile.toml", FINISHER / "lakefile.toml")
    if exists_at(TARGET, "lakefile.toml"):
        write_bytes(FINISHER / "lakefile.de11.original.toml", git_bytes(TARGET, "lakefile.toml"))

    public_api_files = copy_tree(ROOT / "GST", FINISHER / "GST")

    doc_files: list[str] = []
    for doc_subdir in [Path("docs/gst"), Path("docs/problem406")]:
        doc_files += copy_tree(ROOT / doc_subdir, FINISHER / doc_subdir)

    script_files: list[str] = []
    (FINISHER / "scripts").mkdir(exist_ok=True)
    for script_name in ["gst_decl_manifest.py", "problem406_repo_census.py", "create_finisher_bundle.py"]:
        src = ROOT / "scripts" / script_name
        if src.exists():
            shutil.copy2(src, FINISHER / "scripts" / script_name)
            script_files.append(f"scripts/{script_name}")

    ci_files: list[str] = []
    (FINISHER / "ci").mkdir(exist_ok=True)
    for wf in [
        ".github/workflows/final-comparator.yml",
        ".github/workflows/gpt56-problem406-public-api.yml",
        ".github/workflows/gpt56-finalized-de11-census.yml",
        ".github/workflows/gpt56-problem406-theorem-census.yml",
        ".github/workflows/gpt56-finisher-bundle.yml",
    ]:
        src = ROOT / wf
        if src.exists():
            dst = FINISHER / "ci" / Path(wf).name
            shutil.copy2(src, dst)
            ci_files.append(str(dst.relative_to(FINISHER)))

    decls: list[dict[str, object]] = []
    line_counts: dict[str, int] = {}
    for path in source_files:
        text = git_text(TARGET, str(path))
        line_counts[str(path)] = line_count(text)
        clean = strip_comments(text)
        for idx, line in enumerate(clean.splitlines(), 1):
            m = DECL_RE.match(line)
            if not m:
                continue
            name = m.group("name")
            kind = m.group("kind")
            decls.append(
                {
                    "path": str(path),
                    "line": idx,
                    "kind": kind,
                    "name": name,
                    "family": family(str(path), name),
                }
            )

    kinds = Counter(d["kind"] for d in decls)
    theorem_like = [d for d in decls if d["kind"] in {"theorem", "lemma"}]
    families = Counter(str(d["family"]) for d in theorem_like)
    gst_count = families.get("General Space Theory proper", 0)
    total_lines = sum(line_counts.values())

    lock: dict[str, object] = {
        "bundle": "FINISHER",
        "source_target_ref": TARGET,
        "source_target_meaning": "comparator-final source before public API/docs professionalization",
        "current_branch_head_when_generated": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], text=True
        ).strip(),
        "main_monolith": "ErdosTernary2.lean",
        "monolith_lines": line_counts["ErdosTernary2.lean"],
        "custom_import_closure_files": len(source_files),
        "custom_import_closure_lines": total_lines,
        "custom_import_closure_declarations": len(decls),
        "custom_import_closure_declaration_kinds": dict(sorted(kinds.items())),
        "custom_import_closure_theorem_like": len(theorem_like),
        "general_space_theory_proper_theorem_like": gst_count,
        "non_gst_theorem_like": len(theorem_like) - gst_count,
        "theorem_like_families": dict(sorted(families.items())),
        "direct_custom_imports": [m for m in imports(TARGET, MAIN) if not m.startswith(EXTERNAL)],
        "direct_external_imports": [m for m in imports(TARGET, MAIN) if m.startswith(EXTERNAL)],
        "copied_source_files": [str(p) for p in source_files],
        "copied_public_api_files": public_api_files,
        "copied_doc_files": doc_files,
        "copied_script_files": script_files,
        "copied_ci_files": ci_files,
    }

    (FINISHER / "FINISHER.lock.json").write_text(
        json.dumps(lock, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    write_reports(lock, families, line_counts)

    print("FINISHER_BUNDLE_JSON_BEGIN")
    print(json.dumps(lock, indent=2, sort_keys=True))
    print("FINISHER_BUNDLE_JSON_END")
    print(f"FINISHER_SOURCE_REF={TARGET}")
    print(f"FINISHER_MONOLITH_LINES={line_counts['ErdosTernary2.lean']}")
    print(f"FINISHER_CLOSURE_FILES={len(source_files)}")
    print(f"FINISHER_CLOSURE_LINES={total_lines}")
    print(f"FINISHER_THEOREM_LIKE={len(theorem_like)}")
    print(f"FINISHER_GST_PROPER_THEOREM_LIKE={gst_count}")
    print(f"FINISHER_NON_GST_THEOREM_LIKE={len(theorem_like) - gst_count}")


if __name__ == "__main__":
    main()
