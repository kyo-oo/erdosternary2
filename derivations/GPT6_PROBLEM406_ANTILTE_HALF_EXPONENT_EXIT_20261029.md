# Erdős #406 — anti-LTE half-exponent escape route, 2026-10-29

## Exact target and relationship to the single hGate

Original strict target: `∀K≥5, K≠7 → CommonTwo(K)`.
Original production seam: `gst_four_power_third_wave_gate` (same target by proved
third-wave equivalence), still not discharged here.

This route attacks genuinely arbitrarily deep physical survivor exponents:
`H_m=(3^m-1)/2`, all m≥8. Their first m affine ternary digits are
`111...1`, the corresponding actual neighbor affine digits are
`222...2`, so no overlap occurs in those m columns.

### New exact coefficient recurrence

Set
```text
s_m = 2^(3^m)
d_m = (s_m+1)/3^(m+1).
```
Since `s_(m+1)=s_m^3`, inserting `s_m=-1+3^(m+1)d_m`
gives exactly
```text
d_0 = 1
d_(m+1) = d_m + 3^(m+1)*d_m^2*(3^m*d_m-1).
```
The recurrence uses only nonnegative integer operations and proves
`d_(m+1)≡d_m (mod3^(m+1))`. Hence `d_m mod3^9` stabilizes from m=8 onward.

Wolfram and independently written pure Python integer arithmetic give
```text
d_8 mod 3^9 = 8416    (3^9=19683)
e_8=(d_8-1)/2 mod3^9=14049
4*e_8+1 mod3^9=16831
```
At offsets j=0,...,8 above the m-th affine digit:
```text
j:             0 1 2 3 4 5 6 7 8
affine source: 0 0 1 1 2 0 1 0 2
affine next:   1 0 1 2 0 0 2 1 2
```
Their *first* simultaneous two above the prefix is at j=8.
Because the actual power `4^H=1+3 A_H` has its low trit
shifted by one, the first physical shared two is at row `m+9`.

### Exact physical transport

`2H_m+1=3^m`, so
```text
2*4^H_m+1=2^(3^m)+1=3^(m+1)*d_m
2*A_H_m+1=3^m*d_m.
```
Writing `e_m=floor(d_m/2)` (d_m is odd), yields the exact
```text
A_H_m = H_m +3^m*e_m
A_(H_m+1) = (3^m-1)+3^m*(4*e_m+1).
```
The low prefixes are literally all-1 and all-2 respectively, and the
next nine trits are the constants above for all m≥8.

This would prove without hGate:
```lean
∀ m ≥ 8, GSTFourPowerDirectExistence.CommonTwo (halfIndex m)
```
with physical digit witness at row `m+9`.

### Evidence and formalization

- Independent Wolfram exact residue check: d_8=8416 mod3^9,
  e=14049, neighbor=16831, shared source-neighbor trit two
  exactly at offset 8 within these nine digits.
- Pure Python exact `pow(2,3**m,3**(m+10))` confirms
  first hit m+9 for all sampled m=8,...,25,30,40,60,100,200;
  finite experiment only.
- Formal Lean attempt: `GSTProblem406HalfExponentEscape.lean`.
- Strict CI: `.github/workflows/gpt6_406_half_exponent_lte.yml`.
  Check CI success and `#print axioms` before promoting to kernel-verified.

### Pointwise universal hGate boundary

The infinite family `H_m` is NOT a generic surrogate. This result
would resolve the exact gate for an infinite sequence with first-hit
delay tending to infinity, using a new original-source invariant.
It does **not** assert the same for an arbitrary K. The universal
remaining question is whether every eventual-zero natural exponent
trit path beyond {0,1,2,3,4,7} must force some shared 2.
No axiom, informal density, or coefficient stability for this family
can be silently promoted to the full gate.
