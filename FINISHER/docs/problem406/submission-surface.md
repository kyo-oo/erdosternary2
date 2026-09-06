# Problem 406 Submission Surface

This page gives the shortest review path for the Lean artifact.

## Review order

1. Read `questions/deepmind_problem_406/Challenge.lean` for the exact benchmark statement.
2. Read `questions/deepmind_problem_406/Solution.lean` for the submitted theorem bridge.
3. Read `docs/problem406/theorem-map.md` for the clean public naming map.
4. Treat `ErdosTernary2.lean` as the preserved proof artifact that the public surface imports.

## Verification command

```bash
bash scripts/comparator.sh
```

Expected successful verdict:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
Build:   0 errors
Sorries: 0
Status:  CLEAN ✓
```

## Scope statement

The comparator-facing theorem is the arithmetic Problem 406 statement: for all `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`.

## Preservation rule

The accepted monolith is not the presentation layer. It is the protected proof artifact. Presentation work should proceed by small wrapper files, theorem maps, and reviewer documentation before any direct internal refactor.
