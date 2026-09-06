# Reviewer Path

Use this route for the shortest inspection of the Problem 406 artifact.

1. Benchmark statement: `questions/deepmind_problem_406/Challenge.lean`
2. Submitted bridge: `questions/deepmind_problem_406/Solution.lean`
3. Public theorem wrapper: `GST/Problem406/PublicAPI.lean`
4. Compile-checked theorem index: `GST/Problem406/TheoremMap.lean`
5. Preserved proof artifact: `ErdosTernary2.lean`

Run:

```bash
bash scripts/comparator.sh
```

Expected verdict:

```text
Your solution is okay!
=== COMPARATOR RESULT: PASS ===
```
