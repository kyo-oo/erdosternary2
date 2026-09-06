#!/usr/bin/env python3
"""Fix Lean files that place module docstrings before imports.

Lean requires `import` commands to appear before ordinary commands.  A module
docstring `/-! ... -/` is a command, so a professional header must sit after the
import block, not before it.
"""

from __future__ import annotations

from pathlib import Path

ROOT = Path.cwd()
SKIP_PARTS = {".git", ".lake", "ker07-snapshot", "archive", "archives", "snapshots", "__pycache__"}


def fix_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8", errors="replace")
    if not text.startswith("/-!"):
        return False
    end = text.find("-/")
    if end < 0:
        return False
    doc = text[: end + 2].rstrip()
    rest = text[end + 2 :].lstrip("\n")
    lines = rest.splitlines(keepends=True)
    imports: list[str] = []
    i = 0
    while i < len(lines):
        stripped = lines[i].strip()
        if stripped == "":
            imports.append(lines[i])
            i += 1
            continue
        if stripped.startswith("import "):
            imports.append(lines[i])
            i += 1
            continue
        break
    if not any(line.strip().startswith("import ") for line in imports):
        return False
    import_text = "".join(imports).strip() + "\n\n"
    remainder = "".join(lines[i:]).lstrip("\n")
    new_text = import_text + doc + "\n\n" + remainder
    if new_text == text:
        return False
    path.write_text(new_text, encoding="utf-8")
    return True


def tracked_lean_files() -> list[Path]:
    import subprocess

    out = subprocess.check_output(["git", "ls-files", "*.lean"], text=True)
    files = []
    for raw in out.splitlines():
        path = Path(raw)
        if any(part in SKIP_PARTS for part in path.parts):
            continue
        if path.exists():
            files.append(path)
    return sorted(files, key=str)


def main() -> None:
    fixed = [str(path) for path in tracked_lean_files() if fix_file(path)]
    out = ROOT / "docs" / "worldtrace" / "generated" / "lean-import-order-fix.md"
    out.parent.mkdir(parents=True, exist_ok=True)
    rows = "\n".join(f"| `{path}` |" for path in fixed) or "| none |"
    out.write_text(
        f"""# Lean import-order hygiene fix

Lean import commands must precede module docstring commands.  This generated
report lists files whose leading module docstring was moved below the import
block.

| Fixed file |
| --- |
{rows}
""",
        encoding="utf-8",
    )
    print("LEAN_IMPORT_ORDER_FIXED=" + str(len(fixed)))


if __name__ == "__main__":
    main()
