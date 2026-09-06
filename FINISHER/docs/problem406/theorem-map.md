# Problem 406 Theorem Map

This document maps the clean public API plan to the internal fossil artifact.

## Public theorem surface

| Public name | Internal source | Meaning |
|---|---|---|
| `GST.Problem406.contains_two_digit_of_nine_le` | `erdos_ternary_2_universal` in `ErdosTernary2.lean` | For every `n ≥ 9`, the ternary expansion of `2^n` contains digit `2`. |

## Comparator surface

| File | Role |
|---|---|
| `questions/deepmind_problem_406/Challenge.lean` | Benchmark statement with intentional challenge-side `sorry`. |
| `questions/deepmind_problem_406/Solution.lean` | Submitted solution bridge importing the green monolith. |
| `ErdosTernary2.lean` | Preserved proof artifact containing the accepted theorem stack. |

## Preservation rule

`ErdosTernary2.lean` is treated as a preserved proof artifact. Presentation work should add wrappers, maps, and documentation around it before attempting any direct internal rename or source surgery.

## First reviewer path

1. Check the comparator theorem in `questions/deepmind_problem_406/Solution.lean`.
2. Check the public wrapper once created at `GST/Problem406/PublicAPI.lean`.
3. Check this map to understand which clean public names correspond to internal fossil names.
4. Use `bash scripts/comparator.sh` for the repository comparator verdict.
