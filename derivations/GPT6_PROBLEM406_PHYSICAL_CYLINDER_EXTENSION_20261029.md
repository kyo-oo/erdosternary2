# Problem 406 — unconditional two-trit physical cylinder extension

**Research branch:** `gpt6/problem406-physical-cylinder-extension-20261029`

**Requested target:** `∀ K ≥ 5, K ≠ 7 → CommonTwo K`.
**Result of this route:** an exact unconditional *local existence theorem* in every
finite original exponent-residue cylinder; it does **not** substitute for
the requested pointwise universal theorem.

## Exact source-to-neighbor carry forcing

Let `p ≥ 0`, `N=3^p` and `0≤r<N`. Define

```text
X = r + 8N
Y = 4X+1 = (4r+1)+32N.
```

In ternary, `8=22₃`, so `digit₃(X,p)=digit₃(X,p+1)=2`.
Set `c=floor((4r+1)/N)`. Since `0≤r<N`, `0≤c≤3`.
Then `floor(Y/N)=32+c`; the two next digits of Y are:

| c | 32+c | digit(Y,p) | digit(Y,p+1) | collision |
|---|---|---|---|---|
| 0 | 32 | 2 | 1 | p |
| 1 | 33 | 0 | 2 | p+1 |
| 2 | 34 | 1 | 2 | p+1 |
| 3 | 35 | 2 | 2 | p |

Thus for **every** arbitrary lower prefix r, these two consecutive
high source twos force a physical *affine pair* collision within
positions p and p+1. This is an exact four-case integer proof, checked
with Wolfram integer arithmetic.

## Transfer to real 4-power exponents

Let `A_K = (4^K-1)/3`, where `A_(K+1)=4A_K+1` and
`4^K=1+3A_K`. The repository proves for every p that
`K mod 3^p ↦ A_K mod 3^p` is bijective on `Fin (3^p)`:
- `GSTFourPowerAffinePrefixIsometry.affineOrbit_residue_eq_iff_exponent_residue_eq`
- `GSTFourPowerAffineOntologicalCompleteness.every_affine_prefix_is_physical`
- strict green CI: https://github.com/kyo-oo/erdosternary2/actions/runs/40860951943

Set `r=A_K mod3^p`, `X=r+8*3^p`, and note
`X<9*3^p=3^(p+2)`. The bijection supplies a genuine
nonnegative integer `K'<3^(p+2)` with

```text
A_(K') ≡ X   (mod 3^(p+2)).
```

Since `X≡A_K (mod3^p)`, prefix isometry gives
`K'≡K (mod3^p)`. The physical pair `A_(K'),4A_(K')+1`
matches `X,4X+1` through positions p,p+1. Undoing the
compulsory low-ternary-one shift proves:

```text
∀p K, ∃K', K' mod3^p=K mod3^p
  ∧ ((digit₃(4^K',p+1)=2 ∧ digit₃(4^(K'+1),p+1)=2)
     ∨
     (digit₃(4^K',p+2)=2 ∧ digit₃(4^(K'+1),p+2)=2)).
```

Thus `CommonTwo` exponents are 3-adically dense; indeed, by exact
periodicity of both digit positions, each cylinder has infinitely
many good natural exponents, including arbitrarily large ones.

**Formalization:** `GSTProblem406PhysicalCylinderExtension.lean`,
strict workflow `.github/workflows/gpt6_problem406_physical_cylinder_extension.yml`.
A green run is required before calling this *Lean-verified*.

## Why this is not the universal proof

The successful K' is allowed to depend on p and K. The statement
`∀K ∃K'≡K(mod3^p) : CommonTwo K'` does **not** imply
`∀K : CommonTwo K`. In particular, it does not force the original
fixed K to contain a shared 2. The missing step is to exclude
a single nonexceptional *eventually-zero ternary exponent path*
from surviving the full 4-state carry controller for all depths.

A separate parent-branch entropy theorem already bounds the number
of noncolliding exponent residue prefixes by `7^m` at depth `2m`;
zero Haar measure and density do not force emptiness of the exceptional
natural exponents. Our cylinder theorem supplies the independent
open-density side of the topology, not the pointwise elimination.

Historical comparator PASS still has its previously recorded custom
axiom dependency; this branch does not use or reinstate that axiom.
