# GST Tactic Index

This document explains the custom tactic and macro layer used by General Space Theory (GST). These tools are useful internal proof infrastructure, but they should be presented carefully to reviewers.

## Policy

Custom tactics are allowed, but they should be:

1. isolated in tactic/support files;
2. documented by purpose and scope;
3. avoided in the smallest public theorem wrappers when ordinary proof terms are enough;
4. audited through normal Lean compilation and sorry checks;
5. treated as proof automation, not as mathematical assumptions.

## Current tactic/support surface

| Name | Kind | Source | Role |
|---|---|---|---|
| `nat_lt_four_cases` | theorem | `GSTTactic.lean` | Converts `n < 4` into the four exact cases `0,1,2,3`. |
| `nat_lt_three_cases` | theorem | `GSTTactic.lean` | Converts `d < 3` into the three exact ternary digit cases `0,1,2`. |
| `nat_succ_lt_or_eq` | theorem | `GSTTactic.lean` | Small successor-order helper. |
| `nat_lt_four_imp_eq_two` | theorem | `GSTTactic.lean` | Finite carry elimination helper. |
| `nat_lt_four_imp_one_or_two` | theorem | `GSTTactic.lean` | Finite carry elimination helper. |
| `is_gst_positive` | definition | `GSTTactic.lean` | GST+ state predicate. |
| `is_alt_negative` | definition | `GSTTactic.lean` | ALT- state predicate. |
| `is_null_space` | definition | `GSTTactic.lean` | NULL-space predicate. |
| `gst_omega` | tactic | `GSTTactic.lean` | GST-specific arithmetic/decreasing-goal closer; avoids broad unbounded search in final surgery contexts. |
| `gst_carry_cases` | macro tactic | `GSTTactic.lean` | Expands a bounded carry into finite cases. |
| `gst_digit_cases` | macro tactic | `GSTTactic.lean` | Expands a ternary digit into finite cases. |
| `gst_carry_eq_cases` | macro tactic | `GSTTactic.lean` | Produces carry equality cases without immediate substitution. |
| `gst_origin_residue_cases` | macro tactic | `GSTTactic.lean` | Expands origin residues and clears impossible branches. |
| `gst_end` | tactic | `GSTTactic.lean` | Final residual-branch closer for selected GST gates. |
| `infinity` | macro tactic | `ErdosTernary2.lean` | Historical monolith decision tactic; should not be promoted as a public-facing tactic. |

## Public-facing rule

The public Problem 406 wrapper should remain small and ordinary:

```lean
exact erdos_ternary_2_universal n hn
```

The GST tactic layer should be explained in documentation and used internally where it reduces repetitive finite-state arithmetic. It should not be used to hide the mathematical architecture from reviewers.

## Future cleanup rule

When a theorem is promoted into a clean public API file, prefer a direct proof by existing theorem application. Keep tactic-heavy proofs in their source modules unless the tactic itself is the subject of the module.
