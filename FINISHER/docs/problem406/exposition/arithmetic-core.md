# Problem 406 Arithmetic Core

This layer is intentionally plain arithmetic. It is the reviewer-facing entry point for the formal statement before any GST terminology is used.

## Objects

- `digit3 R p` is the ternary digit of `R` at position `p`.
- `carry4 R p` is the exact carry state at position `p` when the ternary expansion is transported through multiplication by four.
- `noTernaryTwo R` is the predicate used by the comparator surface to express absence of digit `2` in the ternary expansion.
- `CommonTwo K` records that both `4^K` and `4^(K+1)` expose a common digit-two witness at a controlled position.
- `exponentPrefix K p` and `exponentTrit K p` split the exponent into the low-prefix/current-trit/high-suffix components used by the prefix law.

## Professional rule

The public API files give calm aliases and wrapper theorems. They do not copy the proof bodies from the monolith and they do not rename internal declarations in place.

## Endpoint

The public Problem 406 theorem is presented as:

```lean
theorem GST.Problem406.contains_two_digit_of_nine_le
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false
```

This is a clean wrapper around the accepted internal theorem `erdos_ternary_2_universal`.
