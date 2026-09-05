#!/usr/bin/env python3
"""
Legacy Step6 kernel repair script intentionally disabled.

This script used to rewrite ErdosTernary2.lean, remove GSTStep6Close from
lakefile.toml, and delete Step6 tactic wrapper files. That behavior is obsolete
and conflicts with the certified Step6 v2 path.

Current intended state:
- GSTStep6CollisionKernel contains the theorem-backed contradiction kernel.
- GSTStep6Close contains the kernel-first tactic wrapper and self-tests.
- lakefile.toml keeps both GSTStep6Close and GSTStep6CollisionKernel as roots.
"""

print("LEGACY_STEP6_KERNEL_REPAIR_SCRIPT_DISABLED=1")
print("No files changed.")
