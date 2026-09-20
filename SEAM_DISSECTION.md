# SEAM DISSECTION — the transport algebra of the SeedOneWitness seam

New receipts (reproduce: `python3 .verification/seam_dissection_check.py` and
`python3 .verification/seam_dissection2.py`). Pure Python, exact modular arithmetic.

## The seam and its grammar (all green already)

    seam: ∀ s,n ≥ 1, SeedOneWitness (prefixOffset s + 4^(3^s) · canonicalTail (s+1) n)
        ⇔ Navigation (canonicalTail s (1+3n))         [prefix_one_tail_shape + green iff]

## LAW 1 — THE UNIT-TAIL BASE FAMILY (NEW GREEN LEMMA CANDIDATE)

**∀ s ≥ 2: Navigation (lteCoeff s).**

| s | first happy row | carry | lteCoeff s mod 243 |
|---|---|---|---|
| 2 | 4 | 3 | 232 |
| 3 | 7 | 0 | 97 |
| ≥ 4 | 4 | 0 | **178** |

Mechanism: `lteCoeff s ≡ 178 mod 243` for all s ≥ 4 (digit at row 4 = 2 since 178 = 2·81+16;
carry at row 4 = 0 since 178 mod 81 = 16 < 81/4). s = 2, 3 are finite checks.
The ∀s ≥ 4 step is the **cube-lift stabilization** `lteCoeff (s+1) ≡ lteCoeff s mod 3^(s+1)`
(D-D: verified s ∈ 1..20), whose Lean proof is elementary:
`lteCoeff (s+1) = lteCoeff s · (4^(2·3^s) + 4^(3^s) + 1)/3` and
`(4^(2·3^s) + 4^(3^s) − 2) ≡ 0 mod 3^(s+2)` because
`(4^(2·3^s)−1)/3^(s+1) ≡ 2 mod 3` and `lteCoeff s ≡ 1 mod 3` sum to `0 mod 3`.

**This is a happy-cell provider the repo does not have** (the audit found none beyond
K=5,6 base cases and origin rows). It is the base case of the whole descent.

## LAW 2 — THE TWO-ZONE IDENTITY (exact, green-able)

With T = canonicalTail (s+1) n, z_s = prefixOffset s, u_s = lteCoeff s
(so 4^(3^s) = 1 + 3^(s+1)·u_s):

    canonicalTail s (1+3n) = 1 + 3·(z_s + T mod 3^(s+1)) + 3^(s+2)·(T/3^(s+1) + u_s·T)

- **Zone 1** (rows 0..s+1): digits of `1 + 3·(z_s + T mod 3^(s+1))`
- **Zone 2** (rows s+2..): digits of `T/3^(s+1) + u_s·T`

Verified exact on 600 cases (T1). Derivable from green pieces: `prefix_one_tail_shape`
+ `canonical_tail_decomposition`. The child T appears in BOTH zones: low rows perturbed
by the FIXED c-tower digits z_s, full length multiplied by the c-tower u_s.

## LAW 3 — UNIT INHERITANCE (k = v₃(n) large ⇒ parent inherits the unit pin)

If k = v₃(n) ≥ s+1 then T ≡ 0 mod 3^(s+1), so zone 1 = 1 + 3·z_s = lteCoeff s and
zone 2 ≡ 0 mod 3^(k+1): **parent ≡ lteCoeff s mod 3^(k+1)**.
With r_s = the unit witness row (4 for s ≥ 2, s ≠ 3; 7 for s = 3): k ≥ r_s ⇒
**parent happy at row r_s** (Law 1 applied to the parent's own low rows).

Confirmed: s ≥ 4, k ≥ 4 → p* = 4 for all m (T3: s=4,5,6 rows k=4..7 all p=4);
s = 3, k = 7 → p = 7 (T3); s = 2, k ≥ 4 → p = 4 (T2, every m).
This explains and strengthens the monolith's `gst_navigation_constant_large_prefix_witness`
with a mechanism needing only Law 1 + Law 2.

## LAW 4 — ORIGIN TRANSPORT (m ≡ 2 mod 3 family)

n = 3^k·m, m ≡ 2 mod 3: child = 3^k·canonicalTail(s+k+1, m) has its happy cell at
row k (origin row of sheet s+k+1 — green `gst_navigation_origin` — shifted by k).
At s = 1 the parent's happy row = **k+1** (T2: every m ≡ 2 mod 3, k ≥ 3: p = k+1).
Mechanism: zone 2 = 3^(s+2)·(3^(k−s−1)·W + u_s·3^k·W) places W's row-0 digit 2 at
parent row k+1; the carry window is empty (parent mod 3^(k+1) = 7 at s=1), carry = 0.

## LAW 5 — THE DESCENT REDUCTION (the seam = lift + green bases)

seam(s, n) needs the child Navigation(canonicalTail(s+1, n)), and:

- n ≡ 2 mod 3 → child is **origin-green** (row 0 at sheet s+1);
- n ≡ 0 mod 3 → child = 3·canonicalTail(s+2, n/3) → Navigation **shifts** (green lemma);
- n ≡ 1 mod 3, n = 1+3n' → child = seam-object(s+1, n') with **n' < n**;
- n = 1 → child = lteCoeff(s+1) → **unit-green** (Law 1).

So by induction on n, every seam instance reduces to LIFT(s, n) applied to a green base.
The lift is the sole remaining content, and its grammar is the two-zone algebra (Law 2).
Witness rows are SHALLOW: 0 failures, max first-witness row 39 over s ∈ 1..5 × n ∈ 1..160.

## LAW 6 — TRANSPORT OPERATOR STABILIZATION

(z_s, u_s) mod 3^j is constant for all s ≥ j (T4: mod 3^2 from s=2, mod 3^3 from s=3,
mod 3^j from s=j). The zone algebra mod 3^j is therefore s-INDEPENDENT for s ≥ j:
the lift's finite perturbation tables are the same for all large sheets. This is the
c_tower convergence controlling the transport itself.

## REFUTATION ADDENDUM (T6)

No residue class mod 27/81 separates the WCP-violators from canonical tails
(all 27 residues hit by both). The U2D sign-route cannot be repaired by a residue
condition on T — consistent with the verdict: the content is the recursion structure
(Laws 2-5), not a residue class.

## NEXT EXECUTED STEPS

1. Lean: `navigation_unit_tail : ∀ s ≥ 2, Navigation (lteCoeff s)` (Law 1) —
   two finite checks + cube-lift stabilization; push as CI probe.
2. Lean: the two-zone identity (Law 2) from green pieces; then unit-inheritance
   (Law 3) and origin transport (Law 4) as corollaries.
3. The lift: transport law table for small k (finite per (s,k), stabilized in s by Law 6),
   descending by Law 5 into the green bases.
