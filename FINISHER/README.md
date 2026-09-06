# FINISHER

`FINISHER/` is the clean final presentation bundle for the Erdős ternary-2 / Problem 406 Lean project.

It freezes the comparator-final proof source and keeps the professional presentation layer beside it.

## Frozen proof source

Pinned source commit:

```text
de11dc2c5ee340fee1929ba2adc6834a72ab9879
```

Main monolith:

```text
FINISHER/ErdosTernary2.lean
```

The recursive custom import closure is copied into this folder using the original module paths.

## Counts

| Item | Count |
| --- | ---: |
| Main monolith lines | 17041 |
| Custom import-closure files | 74 |
| Custom import-closure lines | 30416 |
| Total declarations | 1791 |
| Theorem-like declarations | 1396 |
| GST-proper theorem-like declarations | 77 |
| Non-GST theorem-like declarations | 1319 |

## Important entrypoints

- `ErdosTernary2.lean` — finalized comparator monolith.
- `THEOREM_FAMILIES.md` — theorem-family map.
- `FINISHER.lock.json` — exact machine-readable lock and census.
- `GST/PublicAPI.lean` — curated public API surface.
- `docs/problem406/` and `docs/gst/` — reviewer-facing documentation.

## Decision

Do not mass-wrap all theorem-like declarations. The professional shape is: frozen corpus, full theorem index, then curated public API over the proof spine.
