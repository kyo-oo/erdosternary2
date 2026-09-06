# Problem 406 Proof Artifact Freeze

This document records the preservation rule for the accepted proof artifact.

## Protected artifact

`ErdosTernary2.lean` is treated as the preserved proof artifact for the current phase.

Do not directly rename internal declarations, delete historical proof material, or rewrite proof bodies inside the monolith during the public presentation phase.

## Clean presentation route

Professionalization proceeds by adding small files around the artifact:

1. `GST/Problem406/PublicAPI.lean` exposes clean public theorem names.
2. `GST/Problem406/TheoremMap.lean` provides compile-checked review anchors.
3. `docs/problem406/theorem-map.md` maps public names to internal fossil names.
4. `docs/problem406/submission-surface.md` gives the external reviewer path.
5. `.github/workflows/gpt56-problem406-public-api.yml` checks the wrapper layer.

## Comparator verdict to preserve

The repository comparator verdict to preserve is:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
Build:   0 errors
Sorries: 0
Status:  CLEAN ✓
```

## Next-phase gate

No direct monolith cleanup starts until the public API wrapper and theorem-map files compile green in CI.
