# GST Problem 406 — sharp physical exponent-peel residual and general 3-adic rigidity

Date: 2026-10-29. Branch: `gpt6/problem406-sharp-peel-residual-20261029`.
Target: prove without a custom axiom `forall K>=5, K!=7 -> CommonTwo K`,
with `CommonTwo K` the ORIGINAL simultaneous ternary two in
`4^K` and `4^(K+1)`.

This checkpoint attacks the previously conditional hGate through the
specific true four-power source. Its new statements are **independent
unconditional algebraic theorems**; they do NOT by themselves prove hGate.

## 1. Exact nonlinear GST peel recurrence

Define `A_K=(4^K-1)/3`, `s_m=(3^m-1)/2`, and
`P(x)=4x+12x^2+12x^3`. Then

```text
 A_(3K+1) = 1+3P(A_K),
 P(x)-x = 3x(2x+1)^2.
```

The exact divided difference, for all natural s,delta, is

```text
 P(s+delta)=P(s)+delta*G(s,delta)
 G(s,delta)=4+24s+36s^2+12delta+36s*delta+12delta^2,
 G(s,delta) == 1 (mod 3).
```

Because `s_(m+1)=3s_m+1` and `2s_m+1=3^m`, if

```text
 A_(s_m)=s_m+3^(m+2)*d_m,
```

then direct polynomial substitution gives, for m>=2,

```text
 A_(s_(m+1))=s_(m+1)+3^(m+3)*d_(m+1),
 d_(m+1)=d_m*G(s_m,3^(m+2)*d_m)+3^(m-1)*s_m.
```

Base m=2: s_2=4, A_4=85=4+81, so d_2=1. The nonlinear
gain is 1 (mod3) and 3^(m-1)*s_m is zero (mod3);
hence `d_m == 1 (mod3)` for **ALL** m>=2.
This proves the sharp identity

```text
 v_3(A_(s_m)-s_m)=m+2  (all m>=2).
```

The existing GSTPeelExtraPrecision proved the weaker equality modulo
3^(m+2); this argument proves the NEXT 3-adic digit differs, uniformly,
and identifies the exact normalized leading unit.

Lean module: `GSTProblem406SharpPeelResidual.lean`. The precise
kernel-verification status is the dedicated workflow receipt (do not
promote this to kernel-proved if any run is red).

## 2. Stronger ALL-PHYSICAL-EXPONENT theorem (new mathematical route)

The sharp phenomenon actually holds for **every** natural exponent K
in the entire 3-adic cylinder `K == 4 (mod 9)`, not only `K=s_m`.

For such K, let `m=v_3(2K+1)>=2` and write

```text
 2K+1 = 3^m*q,     q positive, odd, 3 does not divide q.
```

**Theorem (algebraic derivation):**

```text
 v_3(A_K-K) = m+2,
 (A_K-K)/3^(m+2) == q (mod3).
```

This is an unconditional exact identity about genuine powers of 4.

**Proof:** Put `B_m=2^(3^m)` and define the positive integer
`c_m=(B_m+1)/3^(m+1)`. This divisibility is elementary and follows
from LTE or by cubing `B_(m+1)=B_m^3`, starting with B_0=2.
The exact recurrence is

```text
 c_0=1,
 c_(m+1)=c_m-3^(m+1)*c_m^2+3^(2m+1)*c_m^3.
```

The base `c_2=(2^9+1)/27=19`; for m>=2 both correction
terms are divisible by 27, hence

```text
 c_m ==19 (mod27)   (all m>=2).
```

For odd q define `c_(m,q)=(B_m^q+1)/3^(m+1)`. The exact
polynomial identity `z^q+1=(z+1)*(z^(q-1)-z^(q-2)+...-z+1)`
shows `c_(m,q)=c_m*S_q(B_m)`, where `S_q(z)` is that
alternating polynomial and `S_q(-1)=q`.
As `B_m ==-1 (mod 3^(m+1))` and m+1>=3,

```text
 c_(m,q) == q*c_m ==19q (mod27),
 c_(m,q)-q ==18q (mod27).
```

Because 3 does not divide q, the last difference has **exactly**
3-adic valuation 2. Finally use the literal integer identity

```text
 6(A_K-K)=2^(2K+1)+1-3*(2K+1)
         =3^(m+1)*(c_(m,q)-q).
```

It follows that `v_3(A_K-K)=m+2`.
Dividing the displayed identity by `6*3^(m+2)` in integers
gives normalized unit `q (mod3)`, since
`(c_(m,q)-q)/9 ==2q (mod3)`.

Wolfram exact independent checks: m=2..5 and odd 3-free
q in {1,5,7,11,13,17,19}; all 28 pairs agree in both
valuation and normalized residue. These tests validate examples
only, not the universal algebraic proof above.

## 3. Consequences and remaining named implication

The true 3-adic fixedpoint is at `K=-1/2`, with
`A_(-1/2)=-1/2` in the 3-adic continuation of the real
power orbit. The natural all-one exponents `s_m` approximate
it but have a precisely nonzero residual of order m+2.

This eliminates the erroneous inference that the GST
fixedpoint approximation is exact through all ternary orders
for any finite `s_m`. But a nonzero residual in the
difference `A_K-K` is not the same as a simultaneous digit
two of `A_K` and `4A_K+1`. The established half-exponent
family has first real pair collision at m+9 for m>=8; linking
the sharp residual unit to a K-dependent collision for EVERY
nonexceptional K remains the core hGate obligation.

Next decisive route: formalize the full cylinder theorem in
Lean using the 3-adic `c_m` recurrence/alternating factor, then
derive a **source-neighbor common-two forcing** condition from
the normalized residual and 4-state carry law. Do not
assume this implication: it must be proved or falsified.

## 4. Decisive adversarial test: no finite offset even at FIXED valuation 2

Do not extrapolate the sharp residual
`v3(A_K-K)=v3(2K+1)+2` into a collision before
`v3(2K+1)+C` for any absolute constant C.

The new strict Lean theorem in
`GSTProblem406FixedValuationArbitraryDelay.lean` proves

```text
 forall B : Nat, exists K : Nat, K>=5
    and (2*K+1)%27=9
    and forall j<B, digit3 (4^K) (j+1) != 2.
```

Dedicated rigorous kernel receipt: **PASS**
https://github.com/kyo-oo/erdosternary2/actions/runs/40904848592.
No custom axiom, no `sorryAx`.

Proof is constructive via the true physical-affine prefix-isometry:
for p=B+3 obtain k0<3^p with
`A_(k0) == 4 (mod 3^p)` from finite-prefix completeness.
Take `K=k0+3^p`. The original source still satisfies
`A_K == 4 (mod3^p)`, so all its first p ternary trits are
the 1,1,0,0,... word of the actual integer 4. It has NO 2
among those positions, so no original source-neighbor CommonTwo.
But `A_K == 4 == A_4 (mod27)` because `A_4=85`;
the kernel-proved exact physical exponent isometry implies
`K==4 (mod27)`. Hence `(2K+1)%27=9`, fixing
`v3(2K+1)=2` while B was arbitrary.

This does **NOT** produce a globally BAD natural exponent:
the witness K depends on B. It proves the sharp-residual
valuation cannot by itself supply an effective uniform
gate-location bound, even at fixed m.

Sample exact physical witnesses, generated using modular powers:
for B around 6, K=409 (K%27=4), and for B around 8,
K=3568 (K%27=4). The Lean theorem is fully unbounded in B,
not a sampling extrapolation.

## 5. Independent uniform sharp-residual finite audit

`scripts/gst_406_sharp_residual_uniform_audit.py`
tests **every** integer K congruent 4 mod9 in 4<=K<250000:
27,778 exponents. For each it independently computes
the true original source quotient from
`pow(4,K,3^(m+4))`, with m=v3(2K+1), and verifies
the entire normalized unit congruence at modulus
3^(m+3). Local exact integer execution returned zero
failures. This supports the symbolic mathematical derivation
and is explicitly NOT a universal proof.

**Exact original open implication remains:**
`forall K>=5, K!=7 -> CommonTwo K`.
The proof must separate each fixed natural K from the
infinite 3-adic survivor set using an exponent-specific
global argument, not just fixed finite state or valuation.
