# Problem 406 CI Dashboard

This dashboard explains how to read the repository checks after the professional public shell is added.

## Authoritative theorem lane

The comparator lane remains the authority for the accepted Problem 406 result. A green comparator means the submitted theorem endpoint still passes the challenge checker.

Expected markers:

```text
Your solution is okay!
Build:   0 errors
Sorries: 0
Status:  CLEAN ✓
=== COMPARATOR RESULT: PASS ===
```

## Public API lane

The public API lane is a presentation and wrapper check. It verifies that reviewer-facing modules compile after their transitive dependencies have been built.

Expected markers:

```text
PROBLEM406_TRANSITIVE_IMPORTS_GREEN=1
PROBLEM406_PUBLIC_API_GREEN=1
GST_PUBLIC_API_GREEN=1
GST_PUBLIC_AUDIT_GREEN=1
```

## Declaration manifest lane

The manifest lane checks that the generated declaration inventory is stable and searchable.

Expected marker:

```text
GST_DECLARATION_MANIFEST_GREEN=1
```

## Red interpretation rule

A red public API lane does not automatically mean the theorem failed. Public API failures should first be read as wrapper/import/CI plumbing problems unless the comparator lane is also red.

## Current hardening applied

The public API workflow now builds the Lean dependency graph before invoking raw file-level `lake env lean` checks. This directly addresses the mechanical `.olean` missing-object failure from the red public-API run.
