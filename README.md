# ErdosTernary2

> Lean 4 formalization workspace for the **Erdős ternary problem**, wired with the
> **V5 Lean Comparator** verification pipeline.

[![Lean](https://img.shields.io/badge/lean-4.33.0-blue)](https://lean-lang.org/)
[![Comparator](https://img.shields.io/badge/comparator-passes-success)](#comparator)

## What's here

A clean Lean 4 project containing proven theorems about ternary (base-3) digits —
the foundation for Erdős-style ternary analysis. **Zero sorries, zero errors** —
verified by the comparator.

### Proven theorems

| Theorem | Statement |
|--------|-----------|
| `lt_three_cases` | `n < 3 → n = 0 ∨ n = 1 ∨ n = 2` |
| `ternary_digit_lt_three` | `d ≤ 2 → d < 3` |
| `empty_foldr_repr_zero` | empty list folds to `0` in base 3 |
| `single_digit_value` | `[d]` folds to `d` in base 3 |
| `two_digit_value` | `[d₁, d₀]` folds to `3·d₁ + d₀` |
| `isTernaryDigit_correct` | digit recognizer ↔ `n < 3` |

## The Comparator

The **lean comparator** (`scripts/comparator.sh`) is the V5 verification gate
referenced by the `maths-researcher` skill. It runs the full pipeline:

```
lake build  →  sorry_check.sh  →  verdict
```

When the build is clean (0 errors) and sorry-free (0 sorries), it prints:

```
========================================
  Your solution is okay!
========================================
  Build:   0 errors
  Sorries: 0
  Status:  CLEAN ✓
```

### Usage

```bash
# 1. (optional) confirm 0 sorries first
./scripts/sorry_check.sh

# 2. run the comparator
./scripts/comparator.sh
```

## Project layout

```
erdosternary2/
├── ErdosTernary2/
│   └── Basic.lean          # proven theorems (0 sorry, 0 error)
├── ErdosTernary2.lean      # library root import
├── Main.lean               # executable entry point
├── scripts/
│   ├── sorry_check.sh      # counts sorries (must return 0)
│   └── comparator.sh       # V5 lean comparator
├── .devcontainer/
│   └── devcontainer.json   # GitHub Codespace config (installs elan)
├── .github/workflows/      # CI
├── lakefile.toml
├── lean-toolchain          # leanprover/lean4:v4.33.0
└── README.md
```

## Codespace

This repo is configured for **GitHub Codespaces**. Open it in a codespace and
`elan` + Lean 4 are installed automatically via `postCreateCommand`, then the
comparator runs to confirm the build is clean.

## Toolchain

- **Lean**: `v4.33.0` (via `lean-toolchain`)
- **elan**: Lean version manager (installed in codespace + locally)
- **lake**: build tool (ships with elan)
