# Public API CI Note

The public API CI lane checks the review-facing Problem 406 wrapper files. The current first version checks:

```text
GST/Problem406/PublicAPI.lean
GST/Problem406/TheoremMap.lean
```

The umbrella module `GST/Problem406.lean` should be included in the lane after fetching the workflow file blob SHA and updating the workflow safely.
