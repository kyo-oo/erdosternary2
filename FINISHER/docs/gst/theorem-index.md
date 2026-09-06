# General Space Theory (GST) theorem index

This index gives a human taxonomy for the large theorem universe in the repository.

The generated manifest records raw declaration coverage. This curated index explains how the theorem space should be read.

## Indexing rule

Not every internal helper lemma should become a public name. The public surface should expose a small stable set of reviewer-facing names, while the broader theorem universe remains grouped by role.

The intended split is:

| Tier | Purpose |
| --- | --- |
| Public theorem surface | Stable names used by reviewers and external users. |
| Major internal theorems | Important structural results supporting the proof architecture. |
| Local helper lemmas | Tactical or arithmetic lemmas used inside proof files. |
| Generated declaration inventory | Full raw coverage for auditing and completeness checks. |

## Group A: Problem 406 theorem layer

Primary public theorem:

```lean
GST.Problem406.contains_two_digit_of_nine_le
```

Internal checked theorem:

```lean
erdos_ternary_2_universal
```

Primary predicate:

```lean
noTernaryTwo
```

Role: final benchmark-facing statement for powers of two.

## Group B: General Space Theory core layer

Representative public concepts:

```lean
GST.Arithmetic.HappyCell
GST.Arithmetic.Navigation
```

Role: gives the proof a structural language of cells, gates, and navigation states.

The complete internal layer also includes the theory objects, graph states, space predicates, and automation hooks used by the monolith and supporting modules.

## Group C: Arithmetic foundation layer

Representative public names:

```lean
GST.Arithmetic.digit3
GST.Arithmetic.prefix_slice_digit_exact
GST.Arithmetic.canonical_tail_state_isomorphism
```

Role: controls ternary digits and exact tail transport.

## Group D: Carry dynamics layer

Representative public names:

```lean
GST.Arithmetic.carry4
GST.Arithmetic.carry4_lt_four
GST.Arithmetic.carry4_forward_exact
GST.Arithmetic.canonical_tail_happy_iff
```

Role: formalizes exact base-three carry evolution under multiplication by four.

## Group E: Four-power common-two layer

Representative public names:

```lean
GST.FourPower.CommonTwo
GST.FourPower.DirectExistence
GST.FourPower.common_two_has_source_two
GST.FourPower.common_two_has_target_two
GST.FourPower.common_two_of_mod9_five_or_six
```

Role: handles rows where both `4^K` and `4^(K+1)` expose ternary digit `2`.

## Group F: Exponent-prefix law layer

Representative public names:

```lean
GST.FourPower.exponentPrefix
GST.FourPower.exponentTrit
GST.FourPower.exponent_prefix_trit_decomposition
GST.FourPower.pow4_pair_from_exponent_trit
GST.FourPower.no_common_two_exponent_trit_obstruction
```

Role: exposes the parametric prefix/trit law controlling common-two obstructions.

## Group G: Provider and certificate bridge layer

Representative public names:

```lean
GST.FourPower.CreationCertificate
GST.FourPower.CreationMaster
GST.FourPower.creation_certificate_to_navigation
GST.FourPower.four_power_navigation_of_master
```

Role: bridges arithmetic witnesses into GST navigation/certificate language.

## Group H: Tactics and automation layer

Representative concepts include GST tactics, arithmetic normalization helpers, carry/digit automation, and proof-closing tactical utilities.

These should be documented in `docs/gst/tactic-index.md` and kept separate from the curated theorem surface.

## Full generated inventory

The raw generated theorem/declaration inventory belongs in:

```text
docs/gst/generated/theorem-manifest.md
docs/gst/generated/declaration-counts.md
```

The generated inventory is the right place for hundreds of internal theorem names. This curated file is the reader-facing map.
