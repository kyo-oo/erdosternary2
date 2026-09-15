# DERIVATION D — D_WORLDTRACE (binomial / carries / empirics → proof strategy)

Task ID 9-d · Lane D_WORLDTRACE · Erdős ternary campaign
Branch `sol/kyo-gate-universe-wire`, clone `/home/z/erdosternary2`.
Every green citation below was verified by my own Read this session (file:line).
Every numeric below comes from a run I executed this session (command + output in §6), or is
labeled [RECEIPTS-FILE] for the sealed machine receipts of Task 7 (read this session), or is
labeled UNVERIFIED (nothing is).

---

## §1 THE TARGET

The form this lane attacks — the tree-escape form, verbatim from the socket
`hTailF_of_feedback` (GSTTheActConstruction.lean:489-491) and the iff
`the_act_iff_feedback` (GSTTheActConstruction.lean:143-146):

```
∀ K : Nat, 8 ≤ K → ∃ j : Nat,
    (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2
```

Plain language: the only powers of 4 with no ternary digit 2 are 4^0 = 1, 4^1 = 4,
4^4 = 256. All six green-equivalent forms (brief §1) are interchangeable; this lane
works where the binomial/carry arithmetic lives.

**Notation** (all green definitions): `digit3 N p = (N / 3^p) % 3`
(GSTCanonicalTailStateIso.lean:9; GSTFourPowerDirectResidue.lean:9) — "row p".
`trit_ℓ(K) := digit3 K ℓ`. The **noise** of the feedback read at level ℓ:

```
noise_ℓ(K) := digit3 (4^(K mod 3^ℓ)) (ℓ+1)
```

so the target reads: **every K ≥ 8 owns a level ℓ with noise_ℓ(K) + trit_ℓ(K) ≡ 2 (mod 3).**
The noise is the carry stream of the binomial sum — made precise in L6 below.

---

## §2 GREEN INVENTORY (every law this derivation uses)

**The tower (cube law).** `lteCoeff` (natural indexing c₀ = 1) with
`pow4_three_power_lte_exact : 4^(3^r) = 1 + 3^(r+1) * lteCoeff r` and
`lteCoeff_mod3_one : lteCoeff r % 3 = 1` — GSTCanonicalTailLTE.lean:9, :16, :44
(duplicated: GSTFourPowerDirectResidue.lean:14, :21, :50; GSTGraphV2HandwrittenExponentialLTE.lean:24, :31, :60;
monolith copy with shifted index: `c` ErdosTernary2.lean:255, `lte_identity` :371).
Strong mod-9 form: `omega_lteCoeff_mod9 : lteCoeff a % 9 = 7 (1 ≤ a)`
GSTGraphV2OmegaWaveLaw.lean:240 (monolith: `c_mod9_all` ErdosTernary2.lean:413, `c_mod9` :424,
`c_mod3` :435). Stabilization: `c_tower_stabilizes : c s % 3^k = c (k+1) % 3^k (k+1 ≤ s)`
ErdosTernary2.lean:2798, `c_mod_eq_c_stable` :2833. Cube machinery: `cubic_expansion`
ErdosTernary2.lean:281, `c_recursion` :293, `lte_cubic_step` :302. Binomial two-term:
`binom_mod_sq_local : ∃ q, (1+x)^b = 1 + b*x + x^2*q` ErdosTernary2.lean:448.

**The worldtrace read.** `prefaced_window_law` GSTClimbInfiniteFamily.lean:149
(rows v+1+j of 4^(3^v·u+r) = rows v+1+j of 4^r + 3^(v+1)·(4^r·c_v·u), for r < 3^v, j ≤ v);
`prefaced_window_full` :184 (same, as the sliced object `4^r/3^(v+1) + 4^r·c_v·u` at row j);
`every_row_is_read` :215. `self_read` GSTTheActConstruction.lean:79;
`row_one_read` :103; `row_one_kill` :115; `cantorian_iff_feedback` :125;
`the_act_iff_feedback` :143; `prefix_unpack` :170; `feedback_fire_of_class` :196;
`noise_window_law` :346; `unique_dead_child` :355; `hTailF_of_feedback` :489.
Cascade instances: `dust_fire_row_five` :230, `cantorian_dust_mod_243` :309,
`dust_fire_row_six` :389, `cantorian_dust_mod_729` :423.

**Digit arithmetic.** `digit3_eq_of_mod_next` GSTFourPowerDirectResidue.lean:77
(row p depends on residue mod 3^(p+1)); `pow4_digit_period` :106 (row p has period 3^p in K);
`pow4_mod3_one` :115; `pow4_exponent_lift_one_digit` :120, `_two_digit` :139,
`_trit_lift_digit` :156. `cascade_universal` ErdosTernary2.lean:461
((4^(3^s·b)−1)/3^(s+1) ≡ b mod 3); `cascade_universal_mod9` :500.
Ω-cut: `omega_cut_digit : digit3 (4^(3^a·core)) (a+1) = core % 3`
GSTGraphV2OmegaWaveLaw.lean:187; `omega_cut_happy_gate` :228; `omegaWaveStep_worldtrace` :119.

**Carry coordinates.** `carry4 (N p) = (4 * (N % 3^p)) / 3^p`, `HappyCell (C d) = d = 2 ∧ (C = 0 ∨ C = 3)`
GSTCanonicalTailStateIso.lean:12, :15; `carry4_forward_exact : carry4 R (p+1) = (carry4 R p + 4 * digit3 R p) / 3`
GSTCanonicalCarryDynamics.lean:18; `carry4_lt_four` :11. Transplanted strip/residue tower
(registered root): `wideCarry_forward_exact` GSTFinalPurePowerResidueTransplant.lean:118,
`stripConservation_exact` :172, `purePowerResidueTower_exact` :290,
`residueStripCarry_is_exact_power_carry` :310, `exactPowerRectangle_conservation` :339.

**Machine receipts** (Task 7, sealed, read this session):
ANY_NUMBER_TILL_INFINITY_RECEIPTS.md — full period 1,594,323; exhaustive below 16,777,216
(only {0,1,4} escape; max fire row 42 at K = 4,538,457); 20,000 random ≤ 10⁹; 137 monsters
up to 19,729 digits; deep hiders 3^777 → 779, 3^3333 → 3335, 3^5000 → 5002; self_read 280/280
at 10^1000; landmarks 4^10^6 = 420,250 twos, first at row 4.

---

## §3 THE DERIVATION

### Part A — the tower law, airtight (the cube-law induction)

**L1 (TOWER, three strengths).** [GREEN (identity + ≡1 mod 3: GSTCanonicalTailLTE.lean:16,:44),
mod-9 form GREEN GSTGraphV2OmegaWaveLaw.lean:240 / ErdosTernary2.lean:413; unified proof NEW]

Define c₀ = 1 and c_{r+1} = c_r + 3^(r+1)·c_r² + 3^(2r+1)·c_r³ (the green `lteCoeff`).
Then for all ℓ ≥ 0:

- (a) **Identity:** 4^(3^ℓ) = 1 + 3^(ℓ+1)·c_ℓ.
- (b) **Tower law:** c_ℓ ≡ 1 (mod 3) for all ℓ ≥ 0. (c₀ = 1, c₁ = 7, c₂ = 9709 — verified §6 E1.)
- (c) **Strong tower law:** c_ℓ ≡ 7 (mod 9) for all ℓ ≥ 1.
- (d) **Stabilization:** for k+1 ≤ s, c_s ≡ c_{k+1} (mod 3^k). Hence c_ℓ converges 3-adically
  to a constant **c_∞** with digit stream (§6 E6) `[1,2,1,0,2,2,0,1,0,2,1,2,…]`.

*Proof.* (a) Induction on ℓ. Base: 4^(3^0) = 4 = 1 + 3·1. Step: 4^(3^(ℓ+1)) = (4^(3^ℓ))³
= (1 + 3^(ℓ+1)·c_ℓ)³ [by (a)] = 1 + 3·3^(ℓ+1)·c_ℓ + 3·3^(2ℓ+2)·c_ℓ² + 3^(3ℓ+3)·c_ℓ³
[cube law (1+u)³ = 1+3u+3u²+u³] = 1 + 3^(ℓ+2)·(c_ℓ + 3^(ℓ+1)·c_ℓ² + 3^(2ℓ+1)·c_ℓ³)
= 1 + 3^(ℓ+2)·c_{ℓ+1}. (This is `lte_cubic_step` + `lte_identity`, ErdosTernary2.lean:302,:371.)

(b) From the recursion: c_{r+1} = c_r + 3^(r+1)·c_r² + 3^(2r+1)·c_r³; both correction terms
are ≡ 0 mod 3 (r+1 ≥ 1, 2r+1 ≥ 1); so c_{r+1} ≡ c_r (mod 3); c₀ = 1. (Green:
`lteCoeff_mod3_one` GSTCanonicalTailLTE.lean:44.)

(c) Same recursion mod 9: for r ≥ 1, r+1 ≥ 2 and 2r+1 ≥ 3, so both corrections are ≡ 0 mod 9;
c_{r+1} ≡ c_r (mod 9) for r ≥ 1; c₁ = (4^3−1)/9 = 7. (Green: `omega_lteCoeff_mod9`
GSTGraphV2OmegaWaveLaw.lean:240; monolith `c_mod9_all` ErdosTernary2.lean:413.)

(d) Green `c_tower_stabilizes` (ErdosTernary2.lean:2798); machine-confirmed §6 E1 for
k ≤ 7, s ≤ 9. The limit c_∞ := lim c_ℓ exists in ℤ₃ and c_ℓ ≡ c_∞ (mod 3^k) for ℓ ≥ k+1. ∎

### Part B — the worldtrace master congruence (binomial theorem = carry structure)

**L2 (WORLDTRACE MASTER CONGRUENCE).** [NEW, proof; green duplicate of its row-slice
`prefaced_window_law` GSTClimbInfiniteFamily.lean:149]

For all K, ℓ ≥ 0, write K = r + 3^ℓ·u with r = K mod 3^ℓ < 3^ℓ. Then

```
4^K ≡ 4^r + 3^(ℓ+1) · (4^r · c_ℓ · u)   (mod 3^(ℓ+2)).
```

*Proof.* 4^K = 4^r · (4^(3^ℓ))^u [Nat.pow_add, Nat.pow_mul] = 4^r · (1 + x)^u with
x = 3^(ℓ+1)·c_ℓ [L1(a)]. Binomial two-term form (green `binom_mod_sq_local`,
ErdosTernary2.lean:448): (1+x)^u = 1 + u·x + x²·Q for some Q ≥ 0. So
4^K = 4^r + 3^(ℓ+1)·(4^r·c_ℓ·u) + 3^(2ℓ+2)·(4^r·c_ℓ²·Q).
Since 2ℓ+2 ≥ ℓ+2 for ℓ ≥ 0, the last term is ≡ 0 (mod 3^(ℓ+2)). ∎

**L3 (SELF-READ AS A ONE-LINE COROLLARY).** [GREEN GSTTheActConstruction.lean:79; the
two-line derivation is NEW]

digit_{ℓ+1}(4^K) = (noise_ℓ(K) + trit_ℓ(K)) mod 3.

*Derivation from L2.* Rows ≤ ℓ+1 agree between 4^K and B := 4^r + 3^(ℓ+1)·(4^r·c_ℓ·u)
because the congruence modulus is 3^(ℓ+2) (green `digit3_eq_of_mod_next`,
GSTFourPowerDirectResidue.lean:77). Then ⌊B/3^(ℓ+1)⌋ = ⌊4^r/3^(ℓ+1)⌋ + 4^r·c_ℓ·u, so
digit_{ℓ+1}(B) = (digit_{ℓ+1}(4^r) + (4^r mod 3)(c_ℓ mod 3)(u mod 3)) mod 3
= (noise_ℓ(K) + 1·1·trit_ℓ(K)) mod 3, using 4^r ≡ 1 (mod 3) (green `pow4_mod3_one` :115)
and L1(b). ∎

**L4 (SECOND-ORDER READ — the carry made explicit).** [NEW, proof; verified §6 E5 on
20,000 random cases, 0 mismatches]

For ℓ ≥ 1 (write v for this level), r < 3^ℓ, u ≥ 0, put
n₁ = digit_{ℓ+1}(4^r) = noise_ℓ, n₂ = digit_{ℓ+2}(4^r) (the parent's next noise), and
β = (4^(r mod 3) · 7 · (u mod 9)) mod 9. Then

```
digit_{ℓ+2}(4^(r + 3^ℓ·u)) = ⌊ ((n₁ + 3·n₂ + β) mod 9) / 3 ⌋.
```

*Proof.* Green `prefaced_window_full` (GSTClimbInfiniteFamily.lean:184) at level ℓ with
j = 1 (needs 1 ≤ ℓ): digit_{ℓ+2}(4^(3^ℓ·u + r)) = digit_1(A + B) where
A = ⌊4^r/3^(ℓ+1)⌋ and B = 4^r·c_ℓ·u. Now digit_1(X) = ⌊X/3⌋ mod 3 = ⌊(X mod 9)/3⌋;
(A + B) mod 9 = (A mod 9 + B mod 9) mod 9; A mod 9 = digit_0(A) + 3·digit_1(A)
= n₁ + 3·n₂ (shifting rows by ℓ+1); B mod 9 = (4^r mod 9)(c_ℓ mod 9)(u mod 9) mod 9
= (4^(r mod 3)·7·(u mod 9)) mod 9, using c_ℓ ≡ 7 (mod 9) for ℓ ≥ 1 [L1(c), green
`omega_lteCoeff_mod9`] and ord₉(4) = 3 (4³ = 64 ≡ 1 mod 9). Combine. ∎

**L5 (NOISE-PAIR EVOLUTION — the dust-tree blade is a level-homogeneous mod-9
computation).** [NEW, proof; verified §6 E5b on 20,000 random cases, 0 mismatches]

For ℓ ≥ 1, alive parent r < 3^ℓ, child = r + t·3^ℓ (t ∈ {0,1,2}):

```
noise_{ℓ+1}(child) = ⌊ ((n₁ + 3·n₂ + (4^(r mod 3)·7·t mod 9)) mod 9) / 3 ⌋,
dead child (fires at row ℓ+1):  t ≡ (2 − n₁) mod 3      [green `unique_dead_child`,
GSTTheActConstruction.lean:355; `feedback_fire_of_class` :196]
```

with n₁ = noise_ℓ(r), n₂ = digit_{ℓ+2}(4^r). The mod-9 increment table
g(s, t) := digit_1(4^s·7·t) (s = r mod 3 = K mod 3), measured §6 E4:

```
            t=0  t=1  t=2
   s=0:      0    2    1
   s=1:      0    0    0
   s=2:      0    1    2
```

*Proof.* noise_{ℓ+1}(child) = digit_{ℓ+2}(4^child) (child < 3^(ℓ+1) so child mod 3^(ℓ+1) =
child); apply L4 with u = t. The dead-child law is the green unique dead child. Level
homogeneity: the tables use only c_ℓ mod 9 = 7 and 4^(r mod 3) mod 9 — both independent
of ℓ for ℓ ≥ 1 [L1(c)]. ∎

**L6 (THE CARRIES ARE THE NOISE — Lucas/binomial interpretation).** [NEW, interpretation
anchored on green]

4^K = (1+3)^K = Σ_{i=0}^{K} C(K,i)·3^i. Lucas mod 3: C(K,i) ≢ 0 (mod 3) iff every trit of i
is ≤ the corresponding trit of K; in particular C(K, 3^ℓ) ≡ trit_ℓ(K) (mod 3)
(the single nonzero-trit selection). Split the sum at i = 3^ℓ with K = r + 3^ℓ·u:

- the **prefix block** (i ranging over K's low ℓ trits) sums to 4^r — the *frozen prefix*;
- the **first-order block** (i = 3^ℓ·j, j < u, in the u-binomial of (4^(3^ℓ))^u) contributes
  exactly 3^(ℓ+1)·(4^r·c_ℓ·u) — the *worldtrace term* read by L2/L3;
- **everything else is divisible by 3^(2ℓ+2)** — the *carry noise beyond the window*,
  invisible at rows ℓ+1..2ℓ+1 and exactly what `prefaced_window_law` discards
  (GSTClimbInfiniteFamily.lean:156-175 uses `binom_two_term` to kill it).

So the "full carry propagation" of the binomial sum, at row ℓ+1, collapses to the single
mod-3 correction noise_ℓ(K) = digit_{ℓ+1}(4^(K mod 3^ℓ)) — and that noise is itself the
same read one level down. The feedback tree IS the carry propagation, iterated. The green
anchor for every piece: `binom_mod_sq_local` (ErdosTernary2.lean:448) +
`prefaced_window_law` (:149). ∎

### Part C — the machine's empirical laws, as lemmas

**L7 (THE n+2 LAW — 3^n fires at row n+2 for all n ≥ 1).** [NEW, proof from green]

For every n ≥ 1: rows 1..n of 4^(3^n) are 0, row n+1 is 1, row n+2 is 2.
For n = 0 (K = 1): 4^1 = 11_3 never fires — the straggler.

*Proof.* By L1(a), 4^(3^n) = 1 + 3^(n+1)·c_n exactly; rows n+1+k = digit_k(c_n) for all
k ≥ 0 (disjoint supports). Rows 1..n vanish (4^(3^n) ≡ 1 mod 3^(n+1)); digit_0(c_n) = 1
[L1(b)]; digit_1(c_n) = ⌊(c_n mod 9)/3⌋ = ⌊7/3⌋ = 2 [L1(c), n ≥ 1]. ∎
(Receipts-file instances: 3^777 → 779, 3^3333 → 3335, 3^5000 → 5002 [RECEIPTS-FILE];
my fresh runs §6 E2a: n = 1..12 all n+2.) This formalizes the machine law
"v₃(4^(3^n) − 1) = n+1 zeroes the first rows; the 2 lands at row n+2": the valuation
statement itself is L1(a)+(b) (4^(3^n) − 1 = 3^(n+1)·c_n with 3 ∤ c_n).

**L8 (2·3^n AT ROW n+1; 3^n − 1 AT ROW 1).** [GREEN, assembly one line]

2·3^n = 3^n·2 with core 2: green `omega_cut_digit` (GSTGraphV2OmegaWaveLaw.lean:187)
gives digit_{n+1}(4^(2·3^n)) = 2 % 3 = 2 — fires at row n+1, all n ≥ 0 (equivalently
`cascade_universal` ErdosTernary2.lean:461 with b = 2). 3^n − 1 ≡ 2 (mod 3): green
`row_one_kill` (GSTTheActConstruction.lean:115) fires at row 1. (§6 E2b/E2d: n = 0..9 and
n = 1..7, exact.) The general cut law, green, subsumes both: for K = 3^a·core, rows 1..a
are 0 and row a+1 = core mod 3 — core ≡ 2 dies at its cut; core ≡ 1 is the dust branch.

**L9 (THE n+4 LAW — 3^n + 1 fires at row n+4 for all n ≥ 3).** [NEW, proof; machine
[RECEIPTS-FILE] had n ∈ {30,50,100,200,500}; my run §6 E2c extends to all n ∈ [3,40]]

Exact statement: first_fire(3^n + 1) = n + 4 for every n ≥ 3; n = 2 fires at row 7 = n+5;
n = 1 is the straggler K = 4 (4^4 = 100111_3, never fires).

*Proof.* 4^(3^n+1) = 4·4^(3^n) = 4 + 3^(n+1)·(4·c_n) — an exact disjoint decomposition
(4 occupies rows 0,1; n ≥ 1 puts the second term at rows ≥ n+1 ≥ 2). Hence
rows n+1+k = digit_k(4·c_n) for all k ≥ 0. By §6 E6, c_n ≡ 16 (mod 81) for all n ≥ 3:
for n ≥ 5 this is forced by green stabilization L1(d) (c_n ≡ c_5 (mod 3^4)), and the
values n = 3, 4 are literal (c₃ = 222399981598543,
c₄ = 24057640120673299065081231814259802792690247621, both ≡ 16 mod 81). Therefore 4·c_n ≡ 4·16 = 64 (mod 81), and 64 = 2101₃, so the digits of 4·c_n
at k = 0..3 are (1, 0, 1, 2): first 2 at k = 3 → fire row n+1+3 = n+4. For n = 2:
4·c₂ = 38836 has its first 2 (beyond k = 0) at k = 4 (c₂ ≡ 70 mod 81, off the stabilized
value) → row 7 = n+5. ∎

**L10 (DEEP-HIDER MASTER LEMMA — the scaled families read j·c_n).** [NEW, proof]

For all j ≥ 1, n ≥ 1: 4^(j·3^n) = 1 + 3^(n+1)·(j·c_n) + 3^(2n+2)·(green remainder), so

```
rows n+1 .. 2n+1 of 4^(j·3^n)  are  digits 0..n of j·c_n.
```

Hence j·3^n fires by row 2n+1 whenever j·c_n owns a ternary 2 among digits 0..n; and for
fixed j the fire row is n + 1 + (first-2 offset of j·c_n) for all large n whenever that
offset ≤ n, because j·c_n ≡ j·c_∞ (mod 3^k) for n ≥ k+1 [L1(d)] — the offset is a
constant of j alone. *Proof:* binomial two-term on (1+3^(n+1)c_n)^j, as L2, with r = 0. ∎
Instances: j = 1 → offset 1 (c_∞ digits [1,2,…]) → row n+2 (L7); j = 2 → 2·c_∞ ≡ 2 mod 3,
offset 0 → row n+1 (L8); j = 4 → 4·c_∞ digits [1,0,1,2,…] → offset 3 → row n+4 (L9).
The boss's "infinite levels at the same observation point" is exactly this: one constant
c_∞ governs every scaled family at every depth.

**L11 (DUST DOUBLING — alive classes mod 3^ℓ = 2^ℓ exactly, the K ≡ 1 branch carries
2^(ℓ−1)).** [NEW, proof from green `unique_dead_child`; green pins through ℓ = 6
(GSTTheActConstruction.lean:254-460); machine through ℓ = 13 [RECEIPTS-FILE]; my fresh
count §6 E3 through ℓ = 10, exact at every level]

*Proof.* Induction on ℓ. Level 1: alive = {0, 1} (2^1); the ≡ 2 branch dies at row 1
(green `row_one_kill`). Step: call "alive at level ℓ" the residues K mod 3^ℓ with rows
1..ℓ of 4^K clean. (i) Alive at ℓ+1 → alive at ℓ (rows 1..ℓ ⊂ rows 1..ℓ+1). (ii) Each
alive parent r < 3^ℓ has exactly ONE dead child t* = (2 − noise_ℓ(r)) mod 3 (green
`unique_dead_child` GSTTheActConstruction.lean:355 + L3): child r + t*·3^ℓ fires at row
ℓ+1 (green `feedback_fire_of_class` :196). So exactly 2 of its 3 children are alive at
ℓ+1. (iii) Distinct parents have disjoint child sets (children agree mod 3^ℓ with their
parent). (iv) Every alive-at-(ℓ+1) residue is a child of its alive parent. Hence
alive(ℓ+1) = 2·alive(ℓ) = 2^(ℓ+1). Per-branch: the same blade applies to parents in any
mod-3 class, so each branch doubles separately; the ≡ 2 branch is empty from level 1;
the ≡ 1 branch (the dust, root trit 1) and the ≡ 0 branch each carry 2^(ℓ−1). ∎

**L12 (THE EXHAUSTIVE FINITE CERTIFICATE — a receipt, not a lemma).** [MACHINE,
RECEIPTS-FILE Task 7] Below 16,777,216 every K ∈ [8, N) fires; only {0,1,4} escape; max
fire row 42 (K = 4,538,457). This is a FINITE checked fact (86,198 dust members scanned
rows 14..400). It certifies the universal statement on a prefix, and it pins where any
counterexample must live (≥ 16,777,216, ≡ one of the 2^(ℓ−1) dust residues at every
level). It is not a proof of the ONE Prop and is not portable to Lean as one theorem
(the bound is not the statement).

### Part D — the 3-adic viewpoint

**L13 (THE 3-ADIC POWER MAP AND THE PERIOD LAW).** [GREEN anchor + NEW assembly]

Green `pow4_digit_period` (GSTFourPowerDirectResidue.lean:106): digit3 (4^(K + 3^p·u)) p =
digit3 (4^K) p — row p of the worldtrace depends only on K mod 3^p. So the map
K ↦ 4^K mod 3^(p+1) is locally constant on 3^p-classes, and the assignment
K ↦ lim_p 4^(K mod 3^p) is a well-defined continuous map ℤ₃ → 1 + 3ℤ₃ — the 3-adic
power function. The self-similar structure the brief asks for is L2:

```
4^(r + 3^ℓ·s) ≡ 4^r · (1 + 3^(ℓ+1)·c_ℓ·s)   (mod 3^(ℓ+2)),
```

with c_ℓ ≡ 1 mod 3 (L1b): one scale of the exponent shifts one row of the power by the
trit carried — the derivative of the 3-adic power map is the constant 1 in the sense of
L3. The dust set (exponents whose every worldtrace read avoids 2) is the set of 3-adic
integers surviving a 2-of-3 blade at every level (L11): a 3-adic Cantor-type set of
3-adic measure lim (2/3)^ℓ = 0. The ONE Prop says: its only members K with 4^K 2-free
in ℕ are 0, 1, 4. In tower language the three stragglers are: K = 0 (4^0 = 1);
K = 1 = 3^0 (c₀ = 1, no digit 2); K = 4 = 3 + 1 (4·c₁ = 28 = 1001_3 — the first-order
read is clean, and the quadratic remainder never repairs it: 4^4 = 256 = 100111_3). ∎

### Part E — the high-digit route (assessed, flagged, bounded)

**L14 (LEADING-DIGIT FAMILY).** [NEW — mathematically a theorem (Weyl 1916); NOT in the
repo: GAP-LEAN; STRUCTURALLY INSUFFICIENT for the ONE Prop — flagged]

α := log₃4 is irrational (4^q = 3^p has no integer solutions). By Weyl equidistribution,
{K·α} is equidistributed mod 1, so the leading ternary digit of 4^K is 2 for a set of K
of natural density log₃(3/2) = 1 − log₃2 ≈ 0.3691 > 0 — infinitely many K, positive
density. Exact count receipt (§6 E7, no floats): 740 of K ∈ [1, 2000] = 37.00%.

VERDICT, stated plainly so it is never re-litigated: this kills infinitely many new
exponents, but at row ⌈K·log₃ 4⌉ — the TOP row. The ONE Prop needs a 2 at SOME row of a
GIVEN K; equidistribution is a density statement about a sequence and is non-effective
for individual K. The high-digit route can never close the act. It is an infinite
complementary family (formalizable if Weyl-for-log₃4 is ever put in Lean), not a route.
No part of §3 Parts A-D depends on it; nothing here presents a heuristic as fact.

### Part F — the failure maps (what must NOT be retried)

1. **The U2D crossing-charge collision (the dead chat's final architecture).**
   `GSTFinalPrefixOneStep6Infinite.lean` and `GSTFinalPrefixOneStep6Boundary.lean` build
   exact telescoping identities (`weighted_cross_mixed_controller_exact`,
   `canonical_controller_boundary_identification`) — real, bookkeeping-exact, and they
   telescope to endpoint terms only. The attempted contradiction
   (`GSTFinalPrefixOneDirectU2DCollision.lean:137-201`) needed
   `weightedCrossPrefix … > 0` (from a child Navigation witness) AND `≤ 0` (from
   all-depth right badness); the `≤ 0` side is proven at
   GSTFinalPrefixOneDirectU2DCollision.lean:137-173 by `trace_state; omega` on a goal
   carrying `Finset.sum` over abstract function arguments — `omega` cannot close such a
   goal; the file is also NOT registered in lakefile.toml roots (only Step6Infinite and
   PurePowerResidueTransplant are). This is a phantom proof. DO NOT RETRY: (a) the
   trace_state/omega step, ever; (b) the collision architecture unless a genuine sign
   lemma for the controller charge (positivity from a Happy top row that survives the
   telescope) is proven first — the identities alone are 0 = 0.
2. **The bad-language magnitude bound (`BadLanguageMagnitudeScratch.lean`).** The
   no-consecutive-22 language bound 8X ≤ 7(9^m − 1) is correct and green-able. Its bridge
   to the actual problem required the hypothesis "complete seeded bad trace"
   (`GSTBadPairS (gstAffineMulCarryS 4 D X j) (gstDigitS X j)` for all j) — an ASSUMED
   global property of a carry stream, never derived from 4^K's actual worldtrace. DO NOT
   RETRY unless the seed link (badness of the actual stream of a specific power) is
   proven; the bound itself is salvage for a different purpose.
3. **The scratch stack (CarryWord, CanonicalPrefix, OriginModulus, CutIntersection,
   ExponentLift).** These are exact Nat identities, NOT failures — they were production-
   transplanted into `GSTFinalPurePowerResidueTransplant.lean` (registered root). The
   failure lived downstream (the collision). Their content (strip carry words, prefix
   residue causality, exponent-trit lift) is already subsumed by the green
   `self_read`/`prefaced_window_full` spine — do not re-derive it a third time.
4. **The monolith's `cross_term_no_carry` family (ErdosTernary2.lean:2259-2325).**
   REMOVED for OOM (raw `decide` on c(4)..c(7) with 45-digit literals). The lesson is
   ledger 033: any literal check on c_ℓ must go through powMod-bounded digits (compute
   c_ℓ mod 3^k, never c_ℓ raw). My L9/L10 follow that law.

---

## §4 GAP AUDIT

**What this derivation proves:** the full worldtrace arithmetic — the tower (L1, all four
strengths), the master congruence (L2), self_read as its corollary (L3), the carry-explicit
second-order read (L4), the level-homogeneous mod-9 noise-pair evolution (L5), the
binomial/Lucas interpretation (L6); and the machine laws as theorems: n+2 for 3^n (L7),
n+1 for 2·3^n and row 1 for 3^n − 1 (L8), n+4 for 3^n + 1 for all n ≥ 3 (L9), the
deep-hider master lemma (L10), dust doubling 2^(ℓ−1) (L11).

**What remains — named:**

- **GAP-1 (THE residual): NO-DUST-THEOREM.** Exact statement:
  `∀ K : Nat, 8 ≤ K → K % 3 = 1 → ¬ (∀ ℓ, (noise_ℓ(K) + trit_ℓ(K)) % 3 ≠ 2)`
  — no 3-free dust core ≥ 8 threads the blade forever. (This plus the green
  `the_act_iff_feedback` + omega-wave coverage of 3-divisible exponents = the ONE Prop.)
  Obstruction, named: the noise-pair evolution (L5) is level-homogeneous mod 9 but NOT
  finite-state closed — computing the child's next-noise n₂' needs a mod-27 read, the
  grandchild a mod-81 read, … the k-th order noise needs c_ℓ mod 3^k (available and
  stabilized, L1d, but unboundedly deep). No finite invariant/witness for "the stabilized
  noise blocks can avoid 2 forever" is known. Candidate attacks (for Lane B/C): (i) a
  finite-state abstraction of the (n₁, n₂, s) machine with a Lyapunov/exhaustion argument;
  (ii) the 3-adic measure argument (dust has measure 0) upgraded from measure to
  emptiness-on-ℕ via the self-similarity L2; (iii) level-by-level cascade compression:
  each new green cascade level (mod 3^ℓ kill lists, the pattern of
  `dust_fire_row_six`) halves the survivors; a uniform-in-ℓ compression lemma would
  finish it. Each is a named open lemma, not a heuristic presented as fact.
- **GAP-2: WEYL-FOR-log₃4-IN-LEAN** (L14's formalization). Independent infinite family;
  off the critical path by the Part E verdict.
- **GAP-3: the ≡ 0 (mod 3) branch's mirror problem.** E3 shows the 3-divisible branch
  also carries 2^(ℓ−1) alive classes; its rows 2..ℓ of 4^(3w) read the LTE-mean stream
  ((4^w − 1)/3)'s digits — a second 2-free problem on the mean. Lane C's wave covers
  the ≡ 2 cores; the ≡ 1 cores of that branch are the same dust problem one scale down.
  Not an independent gap — descent on the 3-adic valuation (green omega-cut machinery)
  reduces it to GAP-1 — but the reduction lemma ("every 3-divisible exponent reduces to
  a 3-free core with the same fire behavior up to scale") should be stated and proven in
  Lane C's file; my L8/L10 supply the arithmetic.

**The strongest route this lane sees to the ONE Prop:** cascade compression (GAP-1
attack (iii)) — because every ingredient is already green in pattern: the uniform kill
engine (`feedback_fire_of_class`) fires a whole congruence class from one literal noise
receipt; the noise receipts are now known to be *stabilized* constants (L1d/L10: the
noise of a deep-scaled prefix is a c_∞-digit read, level-independent); so the missing
step is a *uniform* version of the level-ℓ kill list — prove that the dead classes at
level ℓ+1 are determined by the same stabilized tables as level ℓ (L5's homogeneity is
exactly this at order 2), and that the doubling survivors cannot avoid the blade's
accumulating constraints. That is GAP-1 restated with the smallest possible missing
lemma; everything below it is green or proven here.

---

## §5 LEAN INTEGRATION SKETCH

New module `GSTWorldtraceArithmetic.lean` (registered in lakefile.toml roots BEFORE any
CI step — ledger 046), importing `GSTCanonicalTailLTE`, `GSTClimbInfiniteFamily`,
`GSTTheActConstruction`, `GSTFourPowerDirectResidue`. No monolith bytes.

1. **Namespace-level defs:** `noise (K ℓ : Nat) : Nat := digit3 (4^(K % 3^ℓ)) (ℓ+1)`
   (notation only; all theorems stated with it unfolded where convenient).
2. **L1:** zero new proofs needed — call `GSTCanonicalTailLTE.pow4_three_power_lte_exact`
   (:16), `lteCoeff_mod3_one` (:44); strong form `GSTGraphV2OmegaWaveLaw.omega_lteCoeff_mod9`
   (:240); stabilization `ErdosTernary2.c_tower_stabilizes` (:2798) — or re-prove the
   stabilization inside the new module over `GSTCanonicalTailLTE.lteCoeff` (same 5-line
   induction as c_mod9_all, avoiding a monolith import).
3. **L2:** mirror the proof shape of `prefaced_window_law` (GSTClimbInfiniteFamily.lean:149-
   177): `obtain ⟨q, hq⟩ := binom two-term` → `Nat.pow_add`, `Nat.pow_mul`, then kill the
   quadratic term by `3^(2ℓ+2) ∣ …` and `Nat.add_mod`-style congruence; conclude with
   `GSTFourPowerDirectResidue.digit3_eq_of_mod_next` (:77) for the row forms.
4. **L4/L5:** 9 literal cases each over the table in L5 — same generated-proof shape as
   `dust_fire_row_six` (GSTTheActConstruction.lean:389-415); each case is
   `prefaced_window_full … 1 …` + `omega` on literal mod-9 data. Watch ledger 064
   (no stacked `Nat.mul_mod` in one rw list — single-fire isolation) and 065 (no
   trailing tactic after an auto-closing rw).
5. **L7/L8/L9/L10:** family theorems. L7: `lte_identity`-shape base + `c_mod9` step;
   the digit reads are `⌊(c mod 9)/3⌋` — decide-safe. L9's base cases n = 3, 4 need
   c₃, c₄ mod 81: compute via powMod-bounded iteration (NEVER raw c₄ — 47 digits,
   ledger 033), then one `decide` per residue. L10 is the general statement; L7/L8/L9
   discharge as instances (j = 1, 2, 4).
6. **L11:** counting induction on ℓ with an explicit alive-set function
   `alive (ℓ : Nat) : Finset ℕ` (or a list-based formulation matching the existing
   cascade style); the blade step consumes `unique_dead_child` + `feedback_fire_of_class`;
   the counting is `Finset.card` arithmetic — the per-level doubling is then the
   green-pins' pattern made structural.
7. **Socket:** end the module with the reduced-residual statement of GAP-1
   (`no_dust_theorem` as a hypothesis-consuming theorem mirroring
   `hTailF_of_feedback` GSTTheActConstruction.lean:489) so the module is useful the day
   GAP-1 lands.

---

## §6 VERIFICATION RECEIPTS (all runs this session, verbatim, exact bounds)

Environment: python3, exact big-int, no floats in decisions. Scripts run from
`/home/z/erdosternary2`. Bounds: every run < 10^7 operations, all < 2 s except E7 (~30 s).

**E1 — the c-tower.** `python3 /tmp/worldtrace_D.py` (c_tower(9), checks ℓ ≤ 9):
```
c_0..c_4 = [1, 7, 9709, 222399981598543, 24057640120673299065081231814259802792690247621]
check c_1=7, c_2=9709: True True
4^(3^l) = 1 + 3^(l+1)*c_l, l=0..6: True
c_l % 3 == 1 for l=0..9: True
c_l % 9 == 7 for l>=1, l=1..9: True
stabilization c_s % 3^k = c_{k+1} % 3^k (k=1..7, s=k+1..9): True
c_inf mod 3^8 (= c_9 mod 3^8): 2851 ternary: 10220121
digit stream of c_inf (rows 0..7): [1, 2, 1, 0, 2, 2, 0, 1]
first 2 in c_inf digits: 1
4*c_inf mod 3^8 ternary: 20122101  digits 0..5: [1, 0, 1, 2, 2, 1]
first 2 in 4*c_inf beyond digit 0: 3
```

**E2 — fire rows of the families.** `python3 /tmp/worldtrace_D2.py`:
```
=== E2a: 3^n fire rows (expect n+2 for n>=1) ===
[(1, 3), (2, 4), (3, 5), (4, 6), (5, 7), (6, 8), (7, 9), (8, 10), (9, 11), (10, 12), (11, 13), (12, 14)]
=== E2b: 2*3^n fire rows (expect n+1) ===
[(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (6, 7), (7, 8), (8, 9), (9, 10)]
=== E2c: 3^n + 1 fire rows; offset = fire_row - n ===
[(1, None, 'NONE<=n+60'), (2, 7, 5), (3, 7, 4), (4, 8, 4), (5, 9, 4), …, (40, 44, 4)]
violations of offset 4: [(1, None, 'NONE<=n+60'), (2, 7, 5)]
=== E2d: misc ===
3^n-1 rows: [(1, 1), (2, 1), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1)]
3^100+3^50+1: 54
6^150: 152
```
(E2c full list: every n ∈ [3, 40] has offset exactly 4 — 38/38.)

**E3 — dust/alive counting.** `python3 /tmp/worldtrace_D3.py` (levels 1..10):
```
level  1: alive=    2 (expect 2^1=2)  K%3==1:1 (expect 2^(l-1)=1)  K%3==0:1  K%3==2:0
level  2: alive=    4 …  K%3==1:2 …  K%3==0:2  K%3==2:0
… (exact at every level) …
level 10: alive= 1024 (expect 2^10=1024)  K%3==1:512 (expect 2^(l-1)=512)  K%3==0:512  K%3==2:0
```

**E4 — mod-9 noise-increment table g(s,t) = digit_1(4^s·7·t):**
```
      t=0  t=1  t=2
 s=0:  [0, 2, 1]
 s=1:  [0, 0, 0]
 s=2:  [0, 1, 2]
```

**E5/E5b — the second-order read law and the noise-pair evolution law**
(20,000 random (v, r, u) / (v, r, t), v ∈ [1,6), seed 42):
```
E5: 20000/20000 match, 0 mismatches
E5b: 20000/20000 match, 0 mismatches
```

**E6 — L9 thresholds and deep c_∞ digits.** `python3 /tmp/worldtrace_D4.py` (c_tower(14)):
```
c_n mod 81 for n=1..9: [7, 70, 16, 16, 16, 16, 16, 16, 16]
digits of 4*c_n (k=0..4) for n=1..6:
  n=1: [1, 0, 0, 1, 0]      n=2: [1, 0, 1, 1, 2]      n=3: [1, 0, 1, 2, 1]
  n=4: [1, 0, 1, 2, 2]      n=5: [1, 0, 1, 2, 2]      n=6: [1, 0, 1, 2, 2]
c_inf mod 3^12 digits (k=0..11): [1, 2, 1, 0, 2, 2, 0, 1, 0, 2, 1, 2]
4*c_inf digits (k=0..11):        [1, 0, 1, 2, 2, 1, 0, 2, 1, 2, 0, 1]
```

**E7 — leading ternary digit 2 of 4^K, exact big-int count (no floats), K ∈ [1, 2000]:**
```
K in [1,2000]: leading-2 count = 740 (37.00%), log_3(3/2) = 0.3691
first such K: [3, 7, 11, 14, 15, 18, 19, 22]
```

**Fresh machine stage (in-session, verbatim):** `timeout 115 python3 tools_any_number_infinity.py sparse`:
```
=== STAGE sparse: 20,000 random K in (10^6, 10^9], rows 1..60 ===
sampled 20000 random K in (10^6, 10^9]:
  row  1:   6744 … row 24:      1
max fire row: 24 (at K=956261565)
stragglers past row 60: 0
stage took 0.1s
=== STAGE sparse DONE ===
```

[RECEIPTS-FILE] (Task 7, not re-run by me): period 1,594,323 full enumeration; exhaustive
deep scan of all 86,198 dust members below 16,777,216 (max row 42 at K = 4,538,457,
stragglers exactly {0,1,4}); monsters (max row 98 at 200!; 3^5000 → 5002); selfread
280/280 at 10^1000; landmarks (4^10^6: 420,250 twos, first at row 4).

---

## §7 SELF-AUDIT (ledger-worthy items for the orchestrator)

1. **Carry omission caught (ledger 011 pattern).** My first draft of the second-order
   read added digit_1(A) + digit_1(B) digit-wise — wrong when the position-0 sum
   noise+trit ≥ 3 carries. The correct closed form ⌊((n₁ + 3n₂ + β) mod 9)/3⌋ was fixed
   BEFORE stating L4 and then verified on 20,000 random cases (E5). No claim stated then
   retracted.
2. **Threshold correction (ledger 066 pattern).** I first wrote the n+4 law with
   threshold "n ≥ 5" (the green stabilization bound for mod 81); E2c/E6 showed n = 3, 4
   also give offset 4 (c₃ ≡ c₄ ≡ 16 mod 81, one step ahead of the green bound's
   guarantee). Corrected to n ≥ 3 with n = 3, 4 as literal base cases. Every number in
   L9 is from E2c/E6 verbatim.
3. **Phantom found (for the orchestrator).** `GSTFinalPrefixOneDirectU2DCollision.lean`
   is not a registered lakefile root and its central theorem closes with
   `trace_state; omega` on a Finset.sum goal (lines 172-173) — it must not be built
   upon and should be quarantined or repaired before any Lean integration references it.
   (The other two Step6 files ARE registered and their identities are exact.)
4. **Provenance discipline (ledger 067/068).** All green citations carry file:line from
   my own reads; all numbers are from my runs or explicitly marked [RECEIPTS-FILE];
   the exhaustive-below-16.7M statement is labeled a finite certificate, not a lemma
   (L12), and the equidistribution content of L14 is labeled a theorem-not-in-Lean and
   its structural insufficiency is stated — no heuristic presented as fact.
5. No .lean file was touched, no git command run, no push, no heavy compute
   (all runs bounded, largest ~30 s, exact big-int only).
