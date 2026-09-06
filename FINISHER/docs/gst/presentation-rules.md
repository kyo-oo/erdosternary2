# GST Presentation Rules

These rules govern how General Space Theory (GST) and its supporting theorem families should be presented in this repository.

## Rule 1 — Preserve the fossil artifact

`ErdosTernary2.lean` is the accepted proof artifact. It records a long proof sprint and contains historical names, repeated comments, and tactical structure. Do not clean it directly during presentation work.

Preferred approach:

1. keep the monolith unchanged;
2. add small wrapper modules;
3. add theorem maps and family indexes;
4. verify wrappers in CI;
5. only then plan a proof-preserving refactor.

## Rule 2 — Expand acronyms on first use

First use:

```text
General Space Theory (GST)
```

After that, `GST` is acceptable.

## Rule 3 — Separate mathematical layers

Do not flatten everything into one story. Use this hierarchy:

```text
General Space Theory umbrella
  → canonical digit/carry objects
  → 2D Mixed Emergence and U2D transport
  → GST Graph V2
  → four-power direct arithmetic
  → exponent-prefix/trit obstruction
  → affine channel / Chat-2 realization
  → provider and certificate bridge
  → prefix-one escape
  → Problem 406 certificate
```

## Rule 4 — Public aliases before internal renames

When a theorem has an ugly or historical internal name, do not rename it in place first.

Instead, create a wrapper theorem with a clean public name:

```lean
theorem clean_public_name ... := by
  exact old_internal_name ...
```

Only rename internal declarations after a separate refactor proves that all imports, theorem maps, and CI checks remain green.

## Rule 5 — Classify theorem names

Every theorem belongs to one of four reviewer priorities:

| Priority | Meaning |
|---|---|
| `core` | The theorem is central to the public mathematical story. |
| `support` | The theorem is important but not part of the first review surface. |
| `internal` | The theorem exists to help Lean close the proof. |
| `historical` | The theorem/module records an older proof route, experiment, or surgery stage. |

Only `core` and selected `support` theorems should receive polished public aliases.

## Rule 6 — Keep tactics visible

Custom tactics are proof automation. They are not assumptions.

Document their purpose in `docs/gst/tactic-index.md`, keep them isolated when possible, and avoid using them in tiny public wrapper files unless necessary.

## Rule 7 — Keep claims scoped

The Lean artifact certifies formal theorem statements. Broader philosophical or physics interpretations belong in separate exposition and must be labeled as interpretation or future theory unless separately formalized.

Use sober language in Lean-facing docs. Save dramatic exposition for the LaTeX paper, where it can be argued carefully.

## Rule 8 — Reviewer path stays short

A reviewer should be able to start with:

1. `questions/deepmind_problem_406/Challenge.lean`
2. `questions/deepmind_problem_406/Solution.lean`
3. `GST/Problem406/PublicAPI.lean`
4. `docs/gst/README.md`
5. `docs/gst/proof-dependency-map.md`

The 630+ theorem machinery should be indexed behind that path, not forced on the first page.
