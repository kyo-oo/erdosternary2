# Problem 406 Professionalization Status

Branch: `sol/problem406-professionalization-green-20260906`

Base phase head: `1d0ab65b5e4a8cc338147b6bef058e9a7f612023`

## Phase board

| Phase | Name | Status | Evidence |
|---|---|---|---|
| 0 | GST groundwork docs | Done | Existing `docs/gst/*` architecture files are present. |
| 1 | Master roadmap and freeze rules | Done | `docs/superpowers/plans/2026-09-06-problem406-professionalization-todo.md` exists and freezes `ErdosTernary2.lean`. |
| 2 | Public Lean API shell | Done | `GST/Arithmetic/*`, `GST/FourPower/*`, `GST/Problem406/*`, and `GST/PublicAPI.lean` exist as wrapper modules. |
| 3 | Theorem manifest and declaration counts | Done | `scripts/gst_decl_manifest.py` and `tests/test_gst_decl_manifest.py` exist; CI checks generated manifest files. |
| 4 | Tactic and audit hygiene | Done | `GST/Audit/PublicSurfaceCheck.lean`, `GST/Audit/Problem406AxiomReport.lean`, and `docs/gst/audit-hygiene.md` added. |
| 5 | Human exposition layer | Done | `docs/problem406/exposition/*` added for arithmetic core, GST mechanism, bridge layer, and interpretation boundary. |
| 6 | CI verification and dashboard cleanup | Patched | Public API workflow hardened to build transitive Lean dependencies before raw wrapper checks; dashboard doc added. |
| 7 | Optional monolith split/refactor | Locked | Not started. Requires Phases 1-6 to be green first. |

## Red-fix diagnosis

The red public-API run was not a proof failure. The workflow invoked raw `lake env lean` file checks before imported `.olean` artifacts were guaranteed to exist. The patch makes the lane build the dependency graph first, then run wrapper and audit file checks.

## Monolith status

`ErdosTernary2.lean` was not edited by this recovery branch. This branch continues the professional outer-shell strategy only.
