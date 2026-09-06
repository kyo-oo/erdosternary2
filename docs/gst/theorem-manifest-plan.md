# GST Theorem Manifest Plan

The repository contains hundreds of theorem and definition declarations. A human-maintained flat list would become inaccurate quickly. The long-term solution is a generated theorem manifest plus a hand-written family index.

This file defines how to manage the 630+ theorem surface without rewriting the monolith.

## Manifest shape

The generated manifest should eventually produce one row per declaration:

| Field | Meaning |
|---|---|
| Declaration | Lean declaration name. |
| Kind | `def`, `theorem`, `lemma`, `structure`, `inductive`, `abbrev`, `axiom`, or tactic/macro. |
| Source file | File containing the declaration. |
| Namespace | Lean namespace. |
| Family | One of the GST theorem families in `theorem-family-index.md`. |
| Reviewer priority | `core`, `support`, `internal`, or `historical`. |
| Public alias | Clean wrapper theorem name if one exists. |
| Axiom report | Output category from `#print axioms` or CI audit where available. |
| Notes | Short human explanation. |

## Generation rule

The manifest should be generated from source using a script, not typed by hand. The first script can be simple:

```text
scan *.lean
extract lines starting with def/theorem/lemma/structure/inductive/abbrev/axiom/syntax/elab/macro_rules
emit docs/gst/generated/theorem-manifest.md
```

A later version can use Lean itself to query the environment, but the first pass should be transparent and easy to audit.

## Family classifier

The first classifier can be path/name based:

| Prefix or file pattern | Family |
|---|---|
| `GSTTactic` | GST tactics and finite-state helpers |
| `GSTCanonical*` | Canonical digit/carry state |
| `GST2D*` | 2D Mixed Emergence |
| `GSTU2D*` | U2D and crossing charge |
| `GSTGraphV2*` | GST Graph V2 |
| `GSTFourPowerDirectResidue*` | Four-power residue classifiers |
| `GSTFourPowerExponentTrit*` | Exponent-prefix/trit law |
| `GSTFourPowerAffine*` | Affine channel automaton |
| `GSTFourPowerDirectChat2*` | Chat-2 application surface |
| `GSTFourPower*Provider*` | Provider pipeline |
| `GSTPrefixOne*` | Prefix-one escape/collision family |
| `ErdosTernary2.lean` | Fossil monolith artifact |
| `questions/deepmind_problem_406/*` | Problem 406 comparator surface |

## Public alias rule

Do not alias every theorem. Alias only:

1. final theorem surfaces;
2. named bridge theorems;
3. reusable concepts a reviewer should search for;
4. major theory landmarks such as Graph V2 laws, exponent-prefix law, provider gates, and certificate bridges.

The remaining declarations should stay indexed as internal support.

## Output files

The generated layer should eventually create:

```text
docs/gst/generated/theorem-manifest.md
docs/gst/generated/declaration-counts.md
docs/gst/generated/public-alias-candidates.md
docs/gst/generated/axiom-audit-map.md
```

## Safety rule

Generating an index must not modify Lean proof files. The script may read source files and write Markdown only. Any later automated alias creation requires a separate proof-preserving refactor plan and CI check.
