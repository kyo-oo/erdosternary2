# GST / Worldtrace: infinity-control terminal normal form and noncircular escape attempts

2026-10-29 IST. Scope: Erdős ternary powers of two, and in particular the exact universal target
  forall K>=5, exists p>=1, digit3 (4^K) p = 2.
Status: **not proved**. This document separates proved global machinery from an unresolved universal collision.

## Evidence and repository dependency audit

The legacy "four-power universal Happy Gate" in GSTInfiniteFourPowerNavigation.lean is not a kernel theorem:
isolated workflow #40785543486 fails at power_three_step_collision line 176, and #print axioms contains sorryAx.
The hypotheses are a child Happy gate at (K,3+q) and a fully BAD right edge at (K+3,3+j).
It is a genuine source-dependent cross-column collision question; exact telescope identities, a negative
child jump and nonnegative parent jumps do not by themselves produce a contradictory inequality.
The older gst_omega_termination_s1, _s3, _stable in ErdosTernary2.lean similarly have an unresolved
final contradiction from exact origin/descent/carry identities.

In GSTFinalPrefixOneStep6Infinite.lean the all-Nat controller exists only with an explicitly
assumed hRightBad. Its infinite mass and Past/Future identities are valid conservation equations
and do not imply the conclusion. GSTCoupledControllerCountermodel.lean constructs a noncanonical
all-Nat parent BAD controller with a child Happy event (parent word 2944, child word 46).
Therefore any unconditional transfer theorem must exploit that the *canonical* input is a
specific perfect-power source.

## Exact terminal Ω normal form — kernel-verified

GSTOmegaTerminalNormalForm.lean is kernel green in dedicated run #40790148990.
Let Happy(C,d) := d=2 and C∈{0,3}; affineCarry D X j := (D+4*(X mod 3^j))/3^j.
The existing kernel theorem GSTOmegaAbsorbingZero.finite_seed_eventually_zero yields
for j>=B=D+4X+1 the exact pair (digit X j, affineCarry D X j)=(0,0).

Thus, with NO finite experiments or limiting hypotheses,
  SeededBadTrace D X <-> forall j<B, not Happy(affineCarry D X j,digit X j).
The infinite BAD suffix after B is automatic, not a contradiction.

For any positive A and valid coupled source initial st with st.childCarry=0,
  InfiniteBadCoupledControl A st <-> SeededBadTrace st.parentSeed (st.parentWord A),
hence also iff the finite preterminal BAD predicate above.
This proves that the all-depth controller introduces NO independent exclusion content
beyond its seeded BAD input. For a canonical parent, a new arithmetic exclusion must refute
that BAD input.

GSTOmegaCanonicalBoundaryIff.lean transports the same equivalence to the actual residual
perfect-power source E=residualEnergy s 1 n, width 3^s, base row s+2, using the existing
canonical zero left carry and fully exact graphCoupledState physical invariant.
Check its own CI before marking it kernel-verified.

## No uniform observation horizon — kernel verified

From GSTFourPowerDirectResidue.pow4_digit_period:
  digit3 (4^(m + 3^p*t)) p = digit3 (4^m) p, any p,m,t.
The special m=4 is clean at EVERY ternary digit (4^4=256=(100111)_3).

For arbitrary L,M, choose K=4+3^L(M+5), so K>=max(5,M).
For every p<=L, K=4+3^p*(3^(L-p)*(M+5)); its row-p digit agrees with
4^4, hence no digit two.
GSTOmegaArbitraryDelay.lean, dedicated CI #40790757888 PASS, proves this statement
fully quantified in Lean without sorryAx.

As a result an eventually-zero exponent path does not guarantee *any fixed finite*
terminal escape bound, including a bound uniform over arbitrary natural K.
This in NO way refutes eventual escape at a K-dependent position.

## An exact first-hit theorem for an infinite perfect-power family

Define c_L=(4^(3^L)-1)/3^(L+1). LTE recursion:
 c_(L+1)=c_L+3^(L+1)c_L^2+3^(2L+1)c_L^3.
For L>=2, c_L mod27 = 16. For L>=5, 4^4=256<3^(L+1).
The already kernel-verified whole-block transport gives
 floor(4^(4+u*3^L)/3^(L+1)) mod27 =
 (u*c_L*256) mod27 = 19u mod27, for every u and L>=5.

1. u=1: 19=(201)_3, so the first postcut trits from low to high
   are 1,0,2; earlier trits equal those of 256. The first 2
   is EXACTLY row L+3.
2. u mod3=2: 19u mod3=2. The first 2 is EXACTLY row L+1 for all
   u of that residue and ALL L>=5.
3. u mod27=1: the first three postcut trits equal (201)_3;
   thus the first 2 is EXACTLY at L+3 for every such u and L>=5.

These are two-variable, unbounded (u,L) algebraic results, not enumeration.
Wolfram independent tests: for u=1, L<=22 first p agrees for all L>=5;
for quotient all-u law, 600 exact pairs L in {5,6,10,15,25}, u=1..120
yielded zero failures. This is corroboration, not replacement for proof.

Lean modules: GSTOmegaExactDelayedEscape.lean and
GSTOmegaThreeTritMultiplierLaw.lean with dedicated CI.
Mark these kernel verified ONLY after their workflow is green.

## The precise missing terminal theorem

A true completion must prove for all canonical nonexceptional source states:
  not SeededBadTrace(parentSeed,parentWord).
Equivalently, an actual Happy parent event exists before its provable terminal cutoff.
The terminal normal form makes this quantifier finite *for each source*, but the
cutoff grows with source and no uniform bound exists. A source-specific
well-founded descent, arithmetic/phase obstruction, or rigorous nonnegative
potential impossibility must produce that witness independently of the assumed
parent BAD or the target conjecture.

No equation equating a bad controller to its initial bad trace can discharge
this. Nor can the 2^L perfect-shadow branching, a density-zero theorem,
an eventual-zero tail, or a passing source-only no-sorry build.

## Strict comparator target

The benchmark solution file previously defines
  erdos_ternary_2 (hGate : gst_four_power_third_wave_gate) :
    forall n, 9<=n -> noTernaryDigitTwo (2^n) = false.
Run #40780932923 correctly rejected this type because the challenge requires
the same proposition WITHOUT hGate. The strict comparator must pass only after
the perfect-power terminal exclusion is kernel proved and installed in the
unconditional type.

This work deliberately distinguishes (a) exact mathematics,
(b) kernel-verified Lean, (c) finite Wolfram checks,
(d) failed proof attempts, and (e) the still open universal theorem.
