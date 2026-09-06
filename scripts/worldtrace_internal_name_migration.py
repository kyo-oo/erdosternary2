#!/usr/bin/env python3
"""Dependency-safe internal Worldtrace name migration.

This script performs the first mechanical migration away from historical
agent/tool-era identifiers in the active source tree.

Design rules:

* operate on the current branch, not on the pinned FINISHER proof snapshot;
* rewrite declarations and references consistently across tracked active files;
* rename matching active files with `git mv` so Lean import names stay coherent;
* preserve the frozen proof corpus under `FINISHER/` as generated evidence;
* write an audit manifest before committing;
* keep the transform deterministic and repeatable.

The migration intentionally promotes neutral Worldtrace names rather than trying
to manually edit theorem bodies.
"""

from __future__ import annotations

import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

ROOT = Path.cwd()

TEXT_SUFFIXES = {
    ".lean",
    ".md",
    ".txt",
    ".toml",
    ".yml",
    ".yaml",
    ".py",
    ".json",
}

SKIP_PARTS = {
    ".git",
    ".lake",
    "FINISHER",
    "ker07-snapshot",
    "archive",
    "archives",
    "snapshots",
    "__pycache__",
}

# Identifier-level replacements.  These are safe to apply to Lean source because
# all active files are rewritten together and matching filenames are moved too.
IDENTITY_REPLACEMENTS = [
    ("GPT56", "Worldtrace"),
    ("gpt56", "worldtrace"),
    ("Gpt56", "Worldtrace"),
]

# Presentation-only replacements.  Applied to comments/prose, not executable Lean
# code outside comments.
PRESENTATION_REPLACEMENTS = [
    ("Old Sol", "the earlier proof layer"),
    ("old Sol", "the earlier proof layer"),
    ("younger-Sol", "the later proof layer"),
    ("Younger-Sol", "the later proof layer"),
    ("Boss's", "the local classifier's"),
    ("boss's", "the local classifier's"),
    ("Boss", "local classifier"),
    ("boss", "local classifier"),
]

WORD_HIT_RE = re.compile(r"(?i)(gpt56|gpt-?5\.6|old sol|younger-sol|boss)")
LEAN_COMMENT_RE = re.compile(r"(--.*?$|/-.*?-/)", re.MULTILINE | re.DOTALL)


@dataclass(frozen=True)
class FileChange:
    path: str
    old_path: str | None
    replacements: int
    kind: str


def run(*args: str) -> str:
    return subprocess.check_output(args, text=True)


def tracked_files() -> list[Path]:
    out = run("git", "ls-files")
    files: list[Path] = []
    for raw in out.splitlines():
        path = Path(raw)
        if any(part in SKIP_PARTS for part in path.parts):
            continue
        if path.suffix not in TEXT_SUFFIXES:
            continue
        if not path.exists():
            continue
        files.append(path)
    return sorted(files, key=str)


def replacement_count(before: str, after: str) -> int:
    if before == after:
        return 0
    return len(WORD_HIT_RE.findall(before))


def rewrite_comment_text(text: str) -> str:
    out = text
    for old, new in PRESENTATION_REPLACEMENTS:
        out = out.replace(old, new)
    return out


def rewrite_lean_comments(text: str) -> str:
    return LEAN_COMMENT_RE.sub(lambda m: rewrite_comment_text(m.group(0)), text)


def rewrite_text(path: Path, text: str) -> str:
    out = text
    for old, new in IDENTITY_REPLACEMENTS:
        out = out.replace(old, new)

    if path.suffix == ".lean":
        out = rewrite_lean_comments(out)
    else:
        out = rewrite_comment_text(out)
    return out


def migrated_path(path: Path) -> Path:
    parts = list(path.parts)
    new_parts = []
    for part in parts:
        new = part
        for old, repl in IDENTITY_REPLACEMENTS:
            new = new.replace(old, repl)
        new_parts.append(new)
    return Path(*new_parts)


def apply_file_moves(files: list[Path]) -> dict[str, str]:
    moves: dict[str, str] = {}
    # Deepest paths first avoids parent/child ordering trouble.
    for path in sorted(files, key=lambda p: len(p.parts), reverse=True):
        new_path = migrated_path(path)
        if new_path == path:
            continue
        if any(part in SKIP_PARTS for part in new_path.parts):
            continue
        new_path.parent.mkdir(parents=True, exist_ok=True)
        if new_path.exists() and new_path != path:
            raise SystemExit(f"refusing to overwrite existing path: {new_path}")
        subprocess.check_call(["git", "mv", str(path), str(new_path)])
        moves[str(new_path)] = str(path)
    return moves


def apply_text_rewrites(files: list[Path], moves: dict[str, str]) -> list[FileChange]:
    changes: list[FileChange] = []
    # Recompute because filenames may have moved.
    for path in tracked_files():
        before = path.read_text(encoding="utf-8")
        after = rewrite_text(path, before)
        if after == before:
            continue
        path.write_text(after, encoding="utf-8")
        changes.append(
            FileChange(
                path=str(path),
                old_path=moves.get(str(path)),
                replacements=replacement_count(before, after),
                kind="rewrite",
            )
        )
    for new_path, old_path in sorted(moves.items()):
        if not any(ch.path == new_path for ch in changes):
            changes.append(FileChange(path=new_path, old_path=old_path, replacements=0, kind="move"))
    return sorted(changes, key=lambda c: c.path)


def remaining_hits() -> list[dict[str, object]]:
    hits: list[dict[str, object]] = []
    for path in tracked_files():
        text = path.read_text(encoding="utf-8", errors="replace")
        for lineno, line in enumerate(text.splitlines(), 1):
            if WORD_HIT_RE.search(line):
                hits.append({"path": str(path), "line": lineno, "text": line[:240]})
    return hits


def write_manifest(changes: list[FileChange], hits: list[dict[str, object]]) -> None:
    out_dir = ROOT / "docs" / "worldtrace" / "generated"
    out_dir.mkdir(parents=True, exist_ok=True)

    data = {
        "migration": "worldtrace-internal-name-migration-v1",
        "scope": "active tracked source and presentation files outside FINISHER/snapshots/archives",
        "changed_files": [ch.__dict__ for ch in changes],
        "remaining_hits": hits,
        "remaining_hit_count": len(hits),
    }
    (out_dir / "internal-name-migration.json").write_text(
        json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    rows = "\n".join(
        f"| `{ch.old_path or ''}` | `{ch.path}` | {ch.kind} | {ch.replacements} |"
        for ch in changes
    ) or "|  |  | no changes | 0 |"
    hit_rows = "\n".join(
        f"| `{hit['path']}` | {hit['line']} | `{str(hit['text']).replace('|', '/')}` |"
        for hit in hits[:100]
    ) or "|  |  | none |"

    (out_dir / "internal-name-migration.md").write_text(
        f"""# Worldtrace internal-name migration report

This report is generated by `scripts/worldtrace_internal_name_migration.py`.

## Scope

Active tracked source and presentation files were migrated away from historical
`GPT56`/`gpt56` identifiers toward neutral `Worldtrace`/`worldtrace` names.

The frozen generated `FINISHER/` bundle, snapshots, and archives are excluded
from direct mutation.  FINISHER should be regenerated by its own workflow after a
successful source migration.

## File changes

| Old path | New/current path | Change kind | Historical hits before rewrite |
| --- | --- | --- | ---: |
{rows}

## Remaining active-tree hits

Remaining hit count: **{len(hits)}**

| Path | Line | Text |
| --- | ---: | --- |
{hit_rows}

## Rule

A nonzero remaining hit count does not automatically fail the migration because
some historical names may survive inside intentionally preserved compatibility
surfaces or external-facing audit prose.  The list above is the dependency-safe
next-pass queue.
""",
        encoding="utf-8",
    )


def main() -> None:
    files = tracked_files()
    moves = apply_file_moves(files)
    changes = apply_text_rewrites(files, moves)
    hits = remaining_hits()
    write_manifest(changes, hits)

    print("WORLDTRACE_INTERNAL_NAME_MIGRATION=1")
    print(f"WORLDTRACE_INTERNAL_NAME_CHANGED_FILES={len(changes)}")
    print(f"WORLDTRACE_INTERNAL_NAME_REMAINING_HITS={len(hits)}")


if __name__ == "__main__":
    main()
