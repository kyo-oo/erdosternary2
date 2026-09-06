# Theorem universe management

The Problem 406 formalization is supported by a large theorem universe. General Space Theory (GST) is the central framework, but it is not the only important layer.

The public documentation should therefore separate:

1. the main General Space Theory framework;
2. the major arithmetic engines that support it;
3. the four-power specialization;
4. provider and certificate bridges;
5. final Problem 406 theorem wrappers;
6. tactical/internal helper lemmas.

## Why not expose every theorem as public API?

A project with hundreds of checked results becomes unreadable if every helper lemma is presented as equally central.

The correct strategy is:

```text
small stable public API
+ curated theorem taxonomy
+ generated raw declaration manifest
```

## Public layer

The public layer contains stable names such as:

```lean
GST.Problem406.contains_two_digit_of_nine_le
GST.Arithmetic.digit3
GST.Arithmetic.carry4
GST.FourPower.CommonTwo
GST.FourPower.exponentPrefix
GST.FourPower.exponentTrit
GST.FourPower.CreationCertificate
```

## Curated layer

The curated layer groups major theorems by role:

| Group | Examples |
| --- | --- |
| General Space Theory core | spaces, cells, navigation, graph language |
| Arithmetic foundation | ternary digits, powers, residues |
| Carry dynamics | exact carry propagation under multiplication by four |
| Four-power engine | common-two witnesses, row filters |
| Prefix law | exponent prefix/trit decomposition and obstruction |
| Provider bridge | conversion from arithmetic witnesses to navigation/certificates |
| Problem 406 | final theorem and predicate bridge |

## Generated layer

The generated layer records broad declaration coverage without forcing every theorem into prose:

```text
docs/gst/generated/theorem-manifest.md
docs/gst/generated/declaration-counts.md
```

This is how the 630+ theorem space stays both auditable and readable.
