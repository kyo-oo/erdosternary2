#!/usr/bin/env python3
"""Generate a declaration manifest for the GST / Problem 406 Lean workspace.

The script is intentionally syntactic. It does not try to elaborate Lean. Its
job is to give reviewers and maintainers a stable index of declarations grouped
by theorem family, while the Lean kernel remains the source of truth for proof
checking.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import argparse
import re
from collections import Counter, defaultdict

DECL_RE = re.compile(
    r"^\s*(?P<visibility>private\s+|protected\s+)?"
    r"(?P<prefix>noncomputable\s+|partial\s+)?"
    r"(?P<kind>theorem|lemma|def|abbrev|structure|inductive|axiom)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_'.]*)"
)

DOC_RE = re.compile(r"^\s*/--(?P<body>.*?) -/\s*$")

SKIP_DIRS = {
    ".git",
    ".lake",
    ".elan",
    "lake-packages",
}


@dataclass(frozen=True)
class Declaration:
    path: str
    line: int
    family: str
    kind: str
    name: str
    visibility: str
    doc: str


def classify_path(path: str) -> str:
    """Classify a Lean file into the public theorem-family taxonomy."""
    name = path.replace("\\", "/")
    base = name.rsplit("/", 1)[-1]

    if name.startswith("GST/Problem406/") or base in {"Problem406.lean"}:
        return "Problem 406 certificate"
    if name.startswith("GST/Arithmetic/") or base in {
        "GSTCanonicalTailStateIso.lean",
        "GSTCanonicalCarryDynamics.lean",
        "GSTFourPowerDirectAdditionCarry.lean",
    }:
        return "Arithmetic core"
    if base.startswith("GSTGraphV2"):
        return "GST Graph V2"
    if base.startswith("GSTU2D") or base == "GST2DMixedEmergence.lean":
        return "U2D and crossing charge"
    if "Affine" in base or "Chat2" in base:
        return "Affine channel automaton"
    if "PrefixOne" in base or "OntologicalEscape" in base or "PerfectPowerTail" in base:
        return "Prefix-one and ontological escape"
    if base.startswith("GSTFourPower") or name.startswith("GST/FourPower/"):
        return "Four-power direct arithmetic"
    if base == "GSTTactic.lean":
        return "Tactics and automation"
    if base == "ErdosTernary2.lean":
        return "Preserved monolith artifact"
    return "Support and historical modules"


def _clean_doc(raw: str) -> str:
    cleaned = raw.strip()
    cleaned = re.sub(r"\s+", " ", cleaned)
    return cleaned


def extract_declarations(path: str, source: str) -> list[Declaration]:
    """Extract top-level Lean declarations from source text."""
    declarations: list[Declaration] = []
    pending_doc = ""
    lines = source.splitlines()

    for index, line in enumerate(lines, start=1):
        doc_match = DOC_RE.match(line)
        if doc_match:
            pending_doc = _clean_doc(doc_match.group("body"))
            continue

        match = DECL_RE.match(line)
        if not match:
            if line.strip() and not line.strip().startswith("@["):
                # Any ordinary nonempty line breaks doc attachment.
                if not line.strip().startswith("/-!") and not line.strip().startswith("--"):
                    pending_doc = ""
            continue

        visibility = (match.group("visibility") or "").strip() or "public"
        declarations.append(
            Declaration(
                path=path,
                line=index,
                family=classify_path(path),
                kind=match.group("kind"),
                name=match.group("name"),
                visibility=visibility,
                doc=pending_doc,
            )
        )
        pending_doc = ""

    return declarations


def iter_lean_files(root: Path) -> list[Path]:
    files: list[Path] = []
    for path in root.rglob("*.lean"):
        if any(part in SKIP_DIRS for part in path.parts):
            continue
        files.append(path)
    return sorted(files)


def collect_declarations(root: Path) -> list[Declaration]:
    declarations: list[Declaration] = []
    for path in iter_lean_files(root):
        rel = path.relative_to(root).as_posix()
        declarations.extend(extract_declarations(rel, path.read_text(encoding="utf-8")))
    return declarations


def write_manifest(declarations: list[Declaration], output: Path) -> None:
    by_family: dict[str, list[Declaration]] = defaultdict(list)
    for declaration in declarations:
        by_family[declaration.family].append(declaration)

    lines: list[str] = []
    lines.append("# GST Declaration Manifest")
    lines.append("")
    lines.append("Generated syntactic declaration index for the GST / Problem 406 Lean workspace.")
    lines.append("")
    lines.append(f"Total declarations: `{len(declarations)}`")
    lines.append("")

    for family in sorted(by_family):
        family_decls = by_family[family]
        lines.append(f"## {family}")
        lines.append("")
        lines.append(f"Declarations: `{len(family_decls)}`")
        lines.append("")
        lines.append("| Kind | Name | File:line | Visibility | Docstring |")
        lines.append("|---|---|---|---|---|")
        for declaration in family_decls:
            doc = declaration.doc.replace("|", "\\|") if declaration.doc else ""
            lines.append(
                f"| `{declaration.kind}` | `{declaration.name}` | "
                f"`{declaration.path}:{declaration.line}` | "
                f"`{declaration.visibility}` | {doc} |"
            )
        lines.append("")

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_counts(declarations: list[Declaration], output: Path) -> None:
    family_counts = Counter(d.family for d in declarations)
    kind_counts = Counter(d.kind for d in declarations)

    lines: list[str] = []
    lines.append("# GST Declaration Counts")
    lines.append("")
    lines.append(f"Total declarations: `{len(declarations)}`")
    lines.append("")
    lines.append("## By family")
    lines.append("")
    lines.append("| Family | Count |")
    lines.append("|---|---:|")
    for family, count in sorted(family_counts.items()):
        lines.append(f"| {family} | {count} |")
    lines.append("")
    lines.append("## By kind")
    lines.append("")
    lines.append("| Kind | Count |")
    lines.append("|---|---:|")
    for kind, count in sorted(kind_counts.items()):
        lines.append(f"| `{kind}` | {count} |")
    lines.append("")

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--manifest",
        type=Path,
        default=Path("docs/gst/generated/theorem-manifest.md"),
    )
    parser.add_argument(
        "--counts",
        type=Path,
        default=Path("docs/gst/generated/declaration-counts.md"),
    )
    args = parser.parse_args()

    declarations = collect_declarations(args.root)
    write_manifest(declarations, args.root / args.manifest)
    write_counts(declarations, args.root / args.counts)
    print(f"GST_DECLARATION_COUNT={len(declarations)}")
    print(f"GST_MANIFEST_WRITTEN={args.manifest}")
    print(f"GST_COUNTS_WRITTEN={args.counts}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
