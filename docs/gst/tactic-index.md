# GST Tactic Index

This document explains the custom tactic and macro layer used by General Space Theory (GST). These tools are useful internal proof infrastructure, but they should be presented carefully to reviewers.

## Policy

Custom tactics are allowed, but they should be:

1. isolated in tactic/support files;
2. documented by purpose, trusted-kernel status, and scope;
3. avoided in the smallest public theorem wrappers when ordinary proof terms are enough;
4. audited through normal Lean compilation and sorry checks;
5. treated as proof automation, not as mathematical assumptions.

## Current tactic/support surface

| Name | Kind | Source | Role | Trusted-kernel status | Reviewer action |
|---|---|---|---|---|---|
| `nat_lt_four_cases` | theorem | `GSTTactic.lean` | Converts `n < 4` into exact cases `0,1,2,3`. | Ordinary theorem checked by Lean. | Inspect only if reviewing finite carry case splits. |
| `nat_lt_three_cases` | theorem | `GSTTactic.lean` | Converts `d < 3` into exact ternary digit cases `0,1,2`. | Ordinary theorem checked by Lean. | Inspect only if reviewing digit case splits. |
| `nat_succ_lt_or_eq` | theorem | `GSTTactic.lean` | Small successor-order helper. | Ordinary theorem checked by Lean. | Low priority helper. |
| `nat_lt_four_imp_eq_two` | theorem | `GSTTactic.lean` | Finite carry elimination helper. | Ordinary theorem checked by Lean. | Inspect with bounded carry eliminations. |
| `nat_lt_four_imp_one_or_two` | theorem | `GSTTactic.lean` | Finite carry elimination helper. | Ordinary theorem checked by Lean. | Inspect with bounded carry eliminations. |
| `is_gst_positive` | definition | `GSTTactic.lean` | GST+ state predicate. | Definition only. | Inspect only for state naming. |
| `is_alt_negative` | definition | `GSTTactic.lean` | ALT- state predicate. | Definition only. | Inspect only for state naming. |
| `is_null_space` | definition | `GSTTactic.lean` | NULL-space predicate. | Definition only. | Inspect only for state naming. |
| `gst_omega` | tactic | `GSTTactic.lean` | GST-specific arithmetic/decreasing-goal closer; avoids broad unbounded search in final surgery contexts. | Expands to Lean proof search/elaboration; kernel still checks generated proof terms. | Inspect implementation if reviewing automation trust surface. |
| `gst_carry_cases` | macro tactic | `GSTTactic.lean` | Expands a bounded carry into finite cases. | Macro/tactic automation; kernel checks resulting proof. | Inspect when reviewing finite carry branching. |
| `gst_digit_cases` | macro tactic | `GSTTactic.lean` | Expands a ternary digit into finite cases. | Macro/tactic automation; kernel checks resulting proof. | Inspect when reviewing finite digit branching. |
| `gst_carry_eq_cases` | macro tactic | `GSTTactic.lean` | Produces carry equality cases without immediate substitution. | Macro/tactic automation; kernel checks resulting proof. | Inspect when reviewing carry equality splits. |
| `gst_origin_residue_cases` | macro tactic | `GSTTactic.lean` | Expands origin residues and clears impossible branches. | Macro/tactic automation; kernel checks resulting proof. | Inspect for residue-case coverage. |
| `gst_end` | tactic | `GSTTactic.lean` | Final residual-branch closer for selected GST gates. | Expands to Lean elaborated proof terms; kernel checks final proof. | Inspect if reviewing branch-closing automation. |
| `infinity` | macro tactic | `ErdosTernary2.lean` | Historical monolith decision tactic. | Internal monolith automation; not public API. | Do not promote as public-facing tactic. |

## Public-facing rule

The public Problem 406 wrapper should remain small and ordinary:

```lean
exact erdos_ternary_2_universal n hn
```

The GST tactic layer should be explained in documentation and used internally where it reduces repetitive finite-state arithmetic. It should not be used to hide the mathematical architecture from reviewers.

## Audit placement rule

Audit-only commands belong in audit modules such as:

- `GST/Audit/PublicSurfaceCheck.lean`
- `GST/Audit/Problem406AxiomReport.lean`

This keeps the public API files calm while preserving reviewer-visible checks.

## Future cleanup rule

When a theorem is promoted into a clean public API file, prefer a direct proof by existing theorem application. Keep tactic-heavy proofs in their source modules unless the tactic itself is the subject of the module.
