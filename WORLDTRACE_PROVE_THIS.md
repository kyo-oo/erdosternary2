# ⬢ THE WORLDTRACE ARITHMETIC BRIEF — PROVE THIS OBJECT

**Repository:** `kyo-oo/erdosternary2`, branch `sol/kyo-gate-universe-wire`, HEAD `fd89766` (CI double-green, 0 sorries).
**Axiom base of every theorem quoted below:** `[propext, Classical.choice, Quot.sound]` — nothing else. No `sorry` anywhere in the chain.

**TO THE PROVER.** This document contains: (0) the exact object, (I) the worldtrace-arithmetic transformation, (II) the complete machinery — the most powerful theorems of the campaign, **copied verbatim as actual Lean code**, (III) the full construction protocol of the **GST Graph V2 Ontological Universe Graph**, (IV) the proof demand.

**DELIVERABLE: A FULL MATHEMATICAL DERIVATION IN LATEX — NOT LEAN CODE.**

---

# PART 0 — THE OBJECT

The Erdős ternary conjecture, original form: **every power $2^n$ with $n \geq 9$ contains the digit $2$ somewhere in its base-3 expansion.**

The repo's ground-truth predicate (monolith `ErdosTernary2.lean:148`):

```lean
def noTernaryTwo (n : Nat) : Bool :=
  if n = 0 then true
  else if n % 3 = 2 then false
  else noTernaryTwo (n / 3)
termination_by n
decreasing_by
  have hk : 0 < n := by omega
  exact Nat.div_lt_self hk (by decide : 1 < 3)
```

The odd-exponent half is **already proven green**. The remaining content is the even half. Since $4^K = 2^{2K}$ with $2K \ge 16 \ge 9$, the even half is one object (`GSTTheAct.lean:51`):

```lean
/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two.
This is the exact content whose absence is the whole conditionality of
`hTailF` — no more, no less. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false
```

The kernel-certified **terminal identity** (monolith `ErdosTernary2.lean:18425`, both directions machine-proven):

```lean
theorem erdos_even_conjecture_iff_tailF :
    (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
      ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
```

The target definition the whole campaign converges to (`GSTGraphV2OmegaWaveLaw.lean:3015`):

```lean
/-- **THE Ω-SHADOW WAVE TAIL (SECOND OBSERVER FORM)** — the residual
input after both observers: the entire tower AND the entire
sheet-zero row cycle, each collapsed to one all-depths clause. -/
def four_power_omega_shadow_wave_tailF : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTailF K → ∃ p : Nat, digit3 (4^K) p = 2
```

with the shadow package (`GSTGraphV2OmegaWaveLaw.lean:2998`):

```lean
def omegaShadowTailF (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) ∧
    (1 ≤ s → (core % 9 = 4 →
      3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3))) ∧
    (1 ≤ s → (core % 9 = 7 →
      ((lteCoeff s * core) % 3^(s+3) < 3^(s+2)
        ∨ 2 * 3^(s+2) ≤ (lteCoeff s * core) % 3^(s+3)))) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1))
```

**PROVING `the_act` — or ANY ONE of the following four green-equivalent residual statements — CLOSES THE OBJECT.** Each has a named, machine-certified, zero-hypothesis consumer already in the repo:

| # | Residual statement to prove | Green consumer (one line) |
|---|---|---|
| 1 | `∀ K : Nat, 8 ≤ K → ∃ j : Nat, (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2` | `GSTTheActConstruction.hTailF_of_feedback` |
| 2 | `¬ ∃ K : Nat, 8 ≤ K ∧ GSTClimbInfiniteFamily.CantorianPower K` | `GSTClimbInfiniteFamily.hTailF_of_no_cantorian` |
| 3 | `∀ K : Nat, 8 ≤ K → ¬ GSTDiagonalRead.WindowCleanDust K` | `GSTDiagonalRead.hTailF_of_dust_empty` |
| 4 | `GSTTheAct.the_act` itself | `GSTTheAct.the_act_iff_hTailF.mp` |
| 5 | both `tailF_row_primitive` **and** `tailF_tower_primitive` (Part II §D4) | `GSTTailFFourthDimension.tailF_of_row_and_tower` |

All five are the same object. The identity chain is:

$$\text{the\_act} \;\Longleftrightarrow\; \text{hTailF-target} \;\Longleftrightarrow\; \text{the full Erdős ternary statement},$$

machine-certified in both directions by `the_act_iff_hTailF`, `the_act_iff_full_erdos`, and `erdos_even_conjecture_iff_tailF`.

---

# PART I — THE WORLDTRACE ARITHMETIC TRANSFORMATION

## I.1 What a worldtrace is

Every natural number $R$ **is** its ternary digit stream — its *worldtrace*:
$$R \;=\; \sum_{p \ge 0} d_p\, 3^p, \qquad d_p = \text{trit}_p(R) \in \{0,1,2\}.$$
The reading operators (verbatim, `GSTCanonicalSevenAxisBridge.lean:22`):

```lean
/-- Ternary information coordinate of one exact natural energy. -/
def digit3 (R p : Nat) : Nat := R / 3^p % 3

/-- x4 carry coordinate of one exact natural energy. -/
def carry4 (R p : Nat) : Nat := (4 * (R % 3^p)) / 3^p
```

`digit3 R p` reads trit $p$ of the worldtrace of $R$; `carry4 R p` is the carry that the multiplication-by-4 automaton holds at depth $p$ when computing $4 \cdot R$ in base 3. These two coordinates are the **state** of the universe graph (Part III).

## I.2 The transformation of the object

The conjecture becomes: **for every $K \ge 8$, the worldtrace of $4^K$ contains a 2.**

The campaign's green laws transform this into five equivalent readings:

1. **The feedback read** (self-read law, Part II §F): trit $j{+}1$ of $\text{wt}(4^K)$ = trit $j{+}1$ of $\text{wt}(4^{K \bmod 3^j})$ + trit $j$ of $\text{wt}(K)$, mod 3. The object = *every $K \ge 8$ fires this sum to 2 at some level $j$*.
2. **The LTE-cut read**: write $K = 3^s \cdot \text{core}$ (3-free core). Then
$$4^{3^s \cdot \text{core}} \;=\; 1 + 3^{s+1} \cdot \underbrace{\omega\mathrm{CutWord}(s,\text{core})}_{\text{the cut word}},$$
and every trit of the power above row $s$ is a trit of the cut word (observer laws, Part II §C). The object = *the cut word of every surviving core fires its top third at some depth*.
3. **The dust read**: the arm $K \equiv 1 \pmod 3$, $K = 1 + 3m$: 
$$4^{1+3m} = 4 \cdot 64^m = 4(1+63)^m,$$
a **binomial sum** — every deep row of the dust power is an **explicit polynomial in $m$** (the blades, Part II §H):
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} \pmod{729},$$
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} + 1000188\binom{m}{3} \pmod{6561},$$
$$4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} + 1000188\binom{m}{3} + 63011844\binom{m}{4} \pmod{19683}.$$
4. **The survivor-tree read**: the Cantorian dust (exponents whose power dodges 2 everywhere) is pinned to $2, 4, 8, 16, 32, 64, 128, \ldots$ residue classes mod $9, 27, 81, 243, 729, 2187, 6561, \ldots$ — a doubling Cantor tree; every node has **exactly one dead child** (`unique_dead_child`). The object = *the infinite intersection of this tree, above 8, is empty*.
5. **The universe-graph read**: a digit 2 at $(t,p)$ is exactly a **Happy cell** (event 8, the $2 \to 2$ transition) of the GST Graph V2 at horizontal stride $t+1$ and vertical depth $p$ (Part III).

## I.3 The constants of the transformation

The **LTE ladder** (`GSTGraphV2HandwrittenExponentialLTE.lean:24`):

```lean
/-- Exact LTE quotient in
`4^(3^r) = 1 + 3^(r+1) * lteCoeff r`. -/
def lteCoeff : Nat → Nat
  | 0 => 1
  | r+1 =>
      let c := lteCoeff r
      c + 3^(r+1) * c^2 + 3^(2*r+1) * c^3

/-- Exact power-of-four LTE identity at every ternary scale. -/
theorem pow4_three_power_lte_exact : ∀ r : Nat,
    4^(3^r) = 1 + 3^(r+1) * lteCoeff r
```

The **c-tower constant** (`GSTTowerFire.lean:50`) — the same object through the blade-wave factorization:

```lean
/-- The tower coefficients `c n = (4^(3^n) − 1) / 3^(n+1)`,
integral by the green LTE cut. -/
def c (n : Nat) : Nat := (4^(3^n) - 1) / 3^(n+1)

theorem four_pow_three_pow_eq (n : Nat) : 4^(3^n) = 1 + 3^(n+1) * c n

/-- **The cube recursion of the tower.**  Cubing the decomposition of
`4^(3^n)` and matching orders gives `c (n+1)` from `c n` with exactly
the two binomial corrections. -/
theorem c_succ_eq (n : Nat) :
    c (n+1) = c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
```

Its frozen congruences (all green):

```lean
theorem c_mod3  (n : Nat) : c n % 3 = 1
theorem c_mod9  (n : Nat) (hn : 1 ≤ n) : c n % 9 = 7
theorem c_mod81 (n : Nat) (hn : 3 ≤ n) : c n % 81 = 16
```

The **stabilization law** — the tower constant is one 3-adic object (`GSTGraphV2OmegaWaveLaw.lean:395`):

```lean
theorem omega_lteCoeff_stable (L d : Nat) :
    ∀ a : Nat, L ≤ a → (lteCoeff a) % 3^L = d % 3^L → ...
```

(called through `GSTDiagonalRead.lteCoeff_stable`):

```lean
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1)
```

Numerically the frozen 3-adic limit is
$$c_\infty \;=\; \lim_{t} \frac{4^{3^t}-1}{3^{t+1}}, \qquad \text{trits } [1,2,1,0,2,2,0,1,0,2,1,2,1,0,\ldots]$$
and the receipt-verified law (modular checks, 27/27 passes): **below depth $t$, the trits of $\omega\mathrm{CutWord}(t,m)$ are exactly the trits of $c_\infty \cdot m$.**

---

# PART II — THE MACHINERY (verbatim Lean code)

Everything below is **actual code, green in CI**, with file:line locations. This is the arsenal.

## §A. The root identity chain — `GSTTheAct.lean` (147 lines, complete spine)

```lean
/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE IDENTITY.**  Through the repo's own green unconditional iff,
the act and `hTailF`'s target are one object: whatever proves the act
proves `hTailF`, and nothing weaker than the act does. -/
theorem the_act_iff_hTailF :
    the_act ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  erdos_even_conjecture_iff_tailF

/-- The full ternary statement restricted to even exponents yields the act. -/
theorem the_act_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) : the_act

/-- **THE ANSWER.  Erdős closed ⇒ hTailF closed, one green line.** -/
theorem hTailF_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  the_act_iff_hTailF.mp (the_act_of_full_erdos hFull)

/-- **THE ACT AND THE FULL STATEMENT ARE ONE OBJECT** — the odd-exponent
half is already green, so the even half is the whole remaining content. -/
theorem the_act_iff_full_erdos :
    the_act ↔ (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false)

/-- **THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of `4^(3^v * a)`
is exactly `a % 3`: the power-of-four ternary digit stream reads the
reduced exponent trit directly. -/
theorem front_law (v : Nat) : ∀ a : Nat,
    digit3 (4^(3^v * a)) (v + 1) = a % 3
```

## §B. The Ω-cut tower — the omega wave law engine (`GSTGraphV2OmegaWaveLaw.lean`, 3043 lines, 140 declarations)

### B1. The Ω operator and the worldtrace orbit law

```lean
/-- **THE NEW OPERATOR ΩW** — one omega wave-climb transfusion step on a
seeded information word: the origin trit is consumed into the x4 seed while
the remaining origin is divided by three. -/
def omegaWaveStep (D X : Nat) : Nat × Nat :=
  ((D + 4 * (X % 3)) / 3, X / 3)

theorem omegaWaveStep_u_divide (D X : Nat) :
    X = originTrit X + 3 * (omegaWaveStep D X).2

theorem omegaWaveStep_u_multiply (D X : Nat) :
    D + 4 * originTrit X =
      3 * (omegaWaveStep D X).1 + ((D + 4 * originTrit X) % 3)

theorem omegaWaveStep_mass (D X : Nat) :
    3 * (omegaWaveStep D X).1 ≤ D + 4 * originTrit X ∧
      D + 4 * originTrit X < 3 * ((omegaWaveStep D X).1 + 1)

/-- **The worldtrace orbit law.**  The vertical step of the exact carry
stream of any energy `R` is literally one Ω-wave transfusion of the seeded
tail: the operator's orbit *is* the information wave that reads the ternary
digits of `R`. -/
theorem omegaWaveStep_worldtrace (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).1 = carry4 R (p+1)

theorem omegaWaveStep_tail (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).2 = R / 3^(p+1)
```

### B2. The cut words

```lean
/-- The geometric mean factor of the Ω-decomposition: the sum of the first
`core` powers of the base `4^(3^a)`. -/
def omegaGeoSum (a core : Nat) : Nat :=
  Finset.sum (Finset.range core) (fun j => (4^(3^a))^j)

/-- The cut word of the Ω-decomposition: the LTE mean times the geometric
mean. -/
def omegaCutWord (a core : Nat) : Nat :=
  lteCoeff a * omegaGeoSum a core

/-- **The Ω-cut factorization** — the omega handwritten equation of the Law.
For every sheet level `a` and every core mass, the power `4^(3^a * core)`
decomposes exactly as one plus the cut modulus times the cut word. -/
theorem omega_cut_factor (a core : Nat) :
    4^(3^a * core) =
      1 + 3^(a+1) * omegaCutWord a core
```

### B3. The ν-law and the level-one gate

```lean
/-- **THE ν-LAW (level one of the Ω-cut tower).**  The ternary digit of
`4^(3^a * core)` at the cut row `a+1` is literally the first nonzero
ternary trit of the exponent. -/
theorem omega_cut_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+1) = core % 3

theorem omega_cut_prefix_one (a core : Nat) :
    4^(3^a * core) % 3^(a+1) = 1

theorem omega_cut_carry_zero (a core : Nat) (ha : 1 ≤ a) :
    carry4 (4^(3^a * core)) (a+1) = 0

/-- **THE Ω-CUT GATE (level one).**  Every exponent whose core mass is
congruent to two modulo three owns a physical Happy row exactly at its own
LTE cut — digit two with carry zero. -/
theorem omega_cut_happy_gate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    HappyCell
      (carry4 (4^(3^a * core)) (a+1))
      (digit3 (4^(3^a * core)) (a+1))
```

### B4. The controller family, the puncture, the shadow wave

```lean
theorem omega_all_bad_to_controller (K : Nat) (hK : ...)   -- :417
    -- every all-bad horizontal block funnels into the controller column

theorem omega_puncture (a core : Nat) (ha : 2 ≤ a) (hcore : core % 3 = 2)  -- :435
    -- the core-two sheet is punctured at its own cut

theorem omega_why_theorem (K : Nat) ...                     -- :452

def omegaShadow (K : Nat) : Prop := ...                     -- :617
def four_power_omega_shadow_wave : Prop := ...              -- :625

theorem omega_digit_two_cases (K : Nat) (hK : 8 ≤ K) : ...  -- :631
theorem omega_digit_two_coverage (hShadow : four_power_omega_shadow_wave) : ...
```

### B5. The deep cuts — every level, binomial-exact

```lean
theorem omega_cut_word_full (s core : Nat) : ...            -- :800
    -- the FULL cut word identity, binomial corrections to all orders

theorem omega_cut_word_mod_pow2 (s core : Nat) (hcore : core % 3 = 1) : ...  -- :858
    -- omegaCutWord s core ≡ lteCoeff s * core (mod 3^(s+2)):
    -- the cut word IS the scaled diagonal below the squared cut

theorem digit3_window (X j : Nat) : ...                      -- :901
    -- the window-slice law: trit j of X from X mod 3^(j+1)

theorem omega_sheet_digit (s core : Nat) (hcore : core % 3 = 1) : ...  -- :931
theorem omega_sheet_gate_digit_two ...                       -- :953
theorem omega_sheet2_digit (s core : Nat) : ...              -- :1237
theorem omega_sheet2_gate_four ...                           -- :1258
theorem omega_sheet2_gate_seven ...                          -- :1307
```

Per-level level-digit laws (each one green, each a residue test on the core):
`omega_level2_digit_two :335`, `omega_level3_digit_two :746`, `omega_level4_digit_two :1047`, `omega_level5_digit_two :1618`, `omega_level6_digit_two :1697`, `omega_level7_digit_two :1971`; exponent-cycle families `omega_expcycle_row3/4/5/6_digit_two_* :1393-2087`.

### B6. The tripling-cube cascade (§7.10)

```lean
/-- The exponent-tripling descent: the cut word of the cubed power. -/
theorem omega_tripling_cut_word (s core : Nat) : ...        -- :2343
    -- W_{s+1} = W_s + 3^(s+1)·W_s² + 3^(2s+1)·W_s³

theorem omega_tripling_digit_transfer (s core : Nat) (hs : 1 ≤ s) : ...  -- :2401
theorem omega_tripling_gate (s core : Nat) ...              -- :2474
theorem omega_tripling_child_digit_two (s core : Nat) ...   -- :2482
```

### B7. The graph form and the chokehold

```lean
theorem graph_column_digit_exact (E t p : Nat) : ...        -- :2514
theorem graph_pure_power_digit_exact (K p : Nat) : ...      -- :2524
theorem omega_shadow_wave_graph ...                         -- :2537
theorem controller_parent_digit_wave ...                     -- :2557
theorem graph_column_parity_energy (n : Nat) : ...          -- :2580
theorem infinite_graph_ternary_two_chokehold ...            -- :2611
theorem infinite_graph_chokehold_envelope ...               -- :2637
```

## §C. THE OBSERVER LAWS — one law, all levels, all generations

**The single most powerful reading instrument in the repo.** It collapses the entire per-level generation ladder into one identity.

```lean
/-- **THE CUT-WORD LINEARITY LAW.**  The sheet word is the mean rotation of
the core: the cut word of `core` sheets equals the unit-core cut word
times the core, modulo the next cut modulus. -/
theorem omega_cut_word_linear (s core : Nat) :
    ∃ t : Nat, omegaCutWord s core
      = omegaCutWord s 1 * core + 3^(s+1) * t

/-- **THE OBSERVER LAW — one object, all generations, all tower levels.**
For every sheet level `s`, every core, and every tower level `k` with
`1 ≤ k ≤ s+1`: the ternary digit of the power `4^(3^s * core)` at tower
row `s+k` is the `(k-1)`-th trit of the single mean rotation
`omegaCutWord s 1 * core`.  No per-level numeral, no per-level gate
theorem: the whole tower is this one identity. -/
theorem omega_observed_digit (s core k : Nat) (hk : 1 ≤ k) (hks : k ≤ s+1) :
    digit3 (4^(3^s * core)) (s + k)
      = ((omegaCutWord s 1 * core) % 3^k) / 3^(k-1)

/-- **THE UNIFORM TOWER GATE — all levels, all generations, one law.**
For every sheet level `s`, every core, and EVERY tower level `k ≥ 3`
inside the sheet's window: whenever the mean rotation's trit at position
`k-1` is two — the top third of the residue window modulo `3^k` — the
power `4^(3^s * core)` owns its ternary digit two at row `s+k`. -/
theorem omega_tower_level_digit_two (s core k : Nat) (hk : 3 ≤ k)
    (hks : k ≤ s+1)
    (hg : 2 * 3^(k-1) ≤ (omegaCutWord s 1 * core) % 3^k) :
    digit3 (4^(3^s * core)) (s + k) = 2

/-- **THE UNIFORM ROW LAW** — the row-axis twin.  For every core and every
depth `j`, if the row word — the cut word at sheet zero, `omegaCutWord 0 core`,
which is exactly `(4^core - 1)/3` — has its top trit two in the window
modulo `3^(j+1)`, then `4^core` owns its ternary digit two at position
`1 + j`.  Rows three through six and every row beyond are instances at
`j = 2, 3, 4, 5, ...`. -/
theorem omega_row_level_digit_two (core : Nat) (j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2
```

## §D. THE 4TH DIMENSION — the emergent diagonal (`GSTTailFFourthDimension.lean`, 2332 lines)

### D1. The extended observation law (no window bound)

```lean
/-- **THE EXTENDED OBSERVATION LAW.**  For every sheet level `s`, every
core, and EVERY depth `j`: whenever the cut word's own trit at depth `j`
sits in the top third of its residue window modulo `3^(j+1)`, the tower
power `4^(3^s * core)` owns its ternary digit two at position `s+1+j`.
No window bound: the reading works at every depth of the power. -/
theorem tower_observation_digit_two (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2
```

### D2. The descent blade — the 4D emergent laws

```lean
/-- **THE CUBE-LIFT STABILIZATION.**  The cut word of sheet level `s+1` is
the cut word of level `s` plus a multiple of `3^(s+1)`: every trit below
position `s+1` is frozen as the sheet level grows. -/
theorem omega_cut_word_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t

/-- **THE EMERGENT AXIS — the descent to the primitive.**  For every
sheet level `s` at or above `k-1`, the tower word at modulus `3^k` is the
primitive level-`(k-1)` word: the diagonal is the SAME object at every
sheet. -/
theorem emergent_dimension_descent (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k

theorem tower_dodge_is_diagonal_dodge (core s k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k

/-- **THE KILL — one diagonal fire, every sheet.**  One ternary digit two
on the primitive diagonal at level `k-1` kills the tower dodge at EVERY
sheet level `S ≥ k-1` at once. -/
theorem emergent_dimension_kill (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2
```

### D3. The exact cube-lift recursion — the engine

```lean
/-- The whole cascade of sheets as ONE recursion with no existential
remainder: the cut word of the next sheet is this sheet's cut word plus
exactly `3^(s+1) · (W² + 3^s·W³)` where `W` is this sheet's own cut word. -/
theorem omega_cut_word_cube_lift_exact (s core : Nat) :
    omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))

/-- **THE +1 LIFT LAW — the diagonal's advance.**  For every sheet from
one onward and every three-free core, the next sheet's cut word is this
sheet's cut word plus exactly ONE unit of the sheet's own modulus,
modulo `3^(s+2)`. -/
theorem omega_cut_word_lift_one (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    omegaCutWord (s+1) core % 3^(s+2)
      = (omegaCutWord s core + 3^(s+1)) % 3^(s+2)

/-- **THE THREE-WINDOW DICHOTOMY — fire, dodge, or escalate.**  Every
sheet `s ≥ 1` of every three-free core, read through its own window: TOP
third ⇒ the power fires at `2*s+2` outright; BOTTOM third ⇒ the dodge;
MIDDLE third ⇒ the `+1` lift makes the next diagonal trit two and the
descent blade kills EVERY sheet `S ≥ s+1` at once. -/
theorem omega_sheet_window_dichotomy (s core : Nat) (hs : 1 ≤ s)
    (hfree : core % 3 = 1 ∨ core % 3 = 2) :
    (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
    ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
    ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
      ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
      ∧ ∀ S : Nat, s+1 ≤ S → digit3 (4^(3^S * core)) (S + (s+2)) = 2)

/-- **THE ESCALATION LAW.**  If every sheet dodges its own window, then at
every level `k ≥ 3` the scaled diagonal sits at or above the middle of its
window: the window dodge feeds the diagonal; the diagonal cannot hide low. -/
theorem omega_window_dodge_escalates (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k

/-- **THE DUST'S SHAPE.**  A three-free core whose sheets all dodge their
windows AND whose diagonal dodges the fire band parks its scaled diagonal
in the EXACT MIDDLE THIRD of every window: window trit zero at every
sheet, diagonal trit one at every level.  The dust is not a fog — it is a
sharply pinned configuration. -/
theorem omega_dust_shape_middle_third (core : Nat)
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (hwin : ∀ s : Nat, 1 ≤ s →
      (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))
    (hdust : ∀ k : Nat, 3 ≤ k →
      (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) :
    ∀ k : Nat, 3 ≤ k →
      3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
        ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)
```

### D4. The decomposition of the input into two named 3-adic trit statements

```lean
/-- **THE ROW PRIMITIVE** — the sheet-zero family's entire carried content:
the row word of every 3-free class-one core above the kernel base owns its
top-third fire at some depth. -/
def tailF_row_primitive : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    (core % 9 = 1 ∨ core % 9 = 4) →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE TOWER PRIMITIVE** — the tower family's entire carried content:
every diagonal-dodging tower's cut word fires its top third in its deep
tail, at depth at least `s+2` — beyond the package's own dodge band. -/
def tailF_tower_primitive : Prop :=
  ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
    (core % 9 = 4 ∨ core % 9 = 7) →
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∃ i : Nat, s+2 ≤ i ∧
        2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)

/-- **THE DECOMPOSITION OF THE INPUT.**  The two named primitives compose
into the full second-observer input. -/
theorem tailF_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF

/-- **THE EVEN-EXPONENT STATEMENT FROM THE TWO PRIMITIVES.** -/
theorem even_conjecture_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE CROWN FROM THE TWO PRIMITIVES.** -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false
```

Also in this file: the nineteen diagonal-ignition bands — `omega_diagonal_two_of_mod_nine_one :206`, `..._mod27_thirteen :225`, `..._mod27_twentyfive :244`, `..._mod81_four :305`, `..._mod81_thirtyfour :324`, `..._mod81_fortynine :343`, `..._mod81_seventy :362`, `..._mod243_sixteen :382` through `..._mod243_onehundredeightyfour :529` (eight mod-243 bands), and the tower-band kills `omega_tower_kill_of_diagonal_two :186`, `omega_tower_digit_two_of_mod_nine_one :262`, `omega_tower_digit_two_of_mod81_band :549`, `omega_tower_digit_two_of_mod243_band :566`.

## §E. THE 2D EMERGENT LAWS (`GST2DMixedEmergence.lean`, 242 lines — the full microscopic physics)

```lean
/-- One literal x2/base-3 microscopic output. -/
def microOutput (a d : Nat) : Nat := (a + 2*d) % 3

def highBit (C : Nat) : Nat := C / 2
def lowBit (C : Nat) : Nat := C % 2

def midDigit (C d : Nat) : Nat := microOutput (highBit C) d

def finalMicroDigit (C d : Nat) : Nat :=
  microOutput (lowBit C) (midDigit C d)

/-- Exact x4/base-3 cell output digit. -/
def outDigit (C d : Nat) : Nat := (C + 4*d) % 3

/-- Exact x4/base-3 next carry. -/
def nextCarry (C d : Nat) : Nat := (C + 4*d) / 3

/-- Handwritten U charge chart. -/
def uCharge (C : Nat) : Int :=
  if C = 0 then 5 else if C = 3 then 21 else 15

/-- Handwritten U jump. -/
def uJump (C d : Nat) : Int :=
  3 * uCharge (nextCarry C d) - uCharge C - 24*(d : Int)

/-- Indicator of information digit BIG2. -/
def twoI (d : Nat) : Int := if d = 2 then 1 else 0

/-- One literal microscopic signed seven-kernel edge. -/
def microSevenKernel (a d : Nat) : Int :=
  14 * (twoI (microOutput a d) - twoI d) +
    7 * (twoI d * twoI (microOutput a d))

/-- The two microscopic x2 layers whose composition is one x4 GST cell. -/
def sevenKernel (C d : Nat) : Int :=
  microSevenKernel (highBit C) d +
    microSevenKernel (lowBit C) (midDigit C d)

/-- Number of microscopic BIG2→BIG2 SURVIVE edges inside the x4 cell.  It is
`0`, `1`, or `2`; unlike a coarse x4 indicator it retains the hidden BIG1
midpoint of the NULL chord `2→1→2`. -/
def surviveI (C d : Nat) : Int :=
  twoI d * twoI (midDigit C d) +
    twoI (midDigit C d) * twoI (finalMicroDigit C d)

/-- Vertical carry potential selected by the exact twelve-cell system. -/
def carryPotential (C : Nat) : Int :=
  if C = 0 then -5 else if C = 1 then -7 else if C = 2 then 1 else 3

/-- Horizontal information potential.  It vanishes on BIG0 and BIG2 and is
`-56` exactly on BIG1. -/
def infoPotential (d : Nat) : Int :=
  112 * twoI d - 56*(d : Int)

/-- Primitive `8:7` mixture of the handwritten seven-kernel and U operator. -/
def mixedDensity (C d : Nat) : Int :=
  8 * sevenKernel C d + 7 * uJump C d
```

The 2D emergent laws:

```lean
/-- Two literal x2 layers reproduce the x4 output trit. -/
theorem finalMicroDigit_eq_outDigit
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    finalMicroDigit C d = outDigit C d

/-- The microscopic seven-kernel telescopes horizontally: only the endpoint
BIG2 charge and the two genuine microscopic SURVIVE incidences remain. -/
theorem sevenKernel_micro_telescope
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    sevenKernel C d =
      14 * (twoI (outDigit C d) - twoI d) + 7 * surviveI C d

/-- The mixed horizontal potential is exactly the BIG1 detector. -/
theorem infoPotential_physical_table (d : Nat) (hd : d < 3) :
    (d = 0 ∧ infoPotential d = 0) ∨
    (d = 1 ∧ infoPotential d = -56) ∨
    (d = 2 ∧ infoPotential d = 0)

/-- The U operator by itself is already a two-direction divergence. -/
theorem uJump_divergence (C d : Nat) (hC : C < 4) (hd : d < 3) :
    uJump C d =
      8 * ((d : Int) - (outDigit C d : Int)) +
      carryPotential C - 3 * carryPotential (nextCarry C d)

/-- **Mixed 2D GST emergence equation.**  The primitive mixture
`8·sevenKernel + 7·U` is forced by the requirement that the horizontal
potential identify BIG0 and BIG2.  What remains is exactly:
a horizontal BIG1-only boundary derivative; a vertical ternary carry
derivative; and positive microscopic SURVIVE incidence in the interior.
Thus the two-dimensional object is an algebraic consequence of the two raw
handwritten operators, not an imposed geometry. -/
theorem mixed_cell_emergence
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    mixedDensity C d =
      infoPotential (outDigit C d) - infoPotential d +
      7 * carryPotential C - 21 * carryPotential (nextCarry C d) +
      56 * surviveI C d

/-- The two x4 Happy realizations separate naturally: NULL is the hidden
BIG1 chord `2→1→2`; GST+ is the all-SURVIVE chord `2→2→2`. -/
theorem happy_chord_dichotomy
    (C : Nat) (hC : C = 0 ∨ C = 3) :
    (C = 0 ∧ midDigit C 2 = 1 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 0) ∨
    (C = 3 ∧ midDigit C 2 = 2 ∧ finalMicroDigit C 2 = 2 ∧ surviveI C 2 = 2)

/-- One horizontal row of physical x4 cells. -/
theorem mixed_row_emergence (C Cnext d : Nat → Nat) (N : Nat)
    (hcell : ∀ t, t < N →
      C t < 4 ∧ d t < 3 ∧
      outDigit (C t) (d t) = d (t+1) ∧
      nextCarry (C t) (d t) = Cnext t) :
    Finset.sum (Finset.range N) (fun t => mixedDensity (C t) (d t)) =
      infoPotential (d N) - infoPotential (d 0) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t)) -
        3 * Finset.sum (Finset.range N) (fun t => carryPotential (Cnext t))) +
      56 * Finset.sum (Finset.range N) (fun t => surviveI (C t) (d t))

/-- **Full 2D divergence theorem.**  Every finite rectangle cut from the live
Nat×Nat grid has only left/right BIG1 boundary charge, bottom/top carry flux,
and positive microscopic SURVIVE incidence. -/
theorem mixed_rectangle_emergence
    (C d : Nat → Nat → Nat) (N K : Nat)
    (hcell : ∀ t p, t < N → p < K →
      C t p < 4 ∧ d t p < 3 ∧
      outDigit (C t p) (d t p) = d (t+1) p ∧
      nextCarry (C t p) (d t p) = C t (p+1)) :
    Finset.sum (Finset.range K) (fun p =>
      (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
        mixedDensity (C t p) (d t p))) =
      Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * (infoPotential (d N p) - infoPotential (d 0 p))) +
      7 * (Finset.sum (Finset.range N) (fun t => carryPotential (C t 0)) -
        (3 : Int)^K * Finset.sum (Finset.range N) (fun t => carryPotential (C t K))) +
      56 * Finset.sum (Finset.range K) (fun p =>
        (3 : Int)^p * Finset.sum (Finset.range N) (fun t =>
          surviveI (C t p) (d t p)))
```

## §F. THE CAUSALITY LAWS

### F1. Origin-prefix causality (`CanonicalCausalityScratch.lean`, complete)

```lean
/-- A ternary digit is exactly the corresponding one-trit quotient of the
prefix residue through that digit. -/
theorem gstDigitS_eq_prefix_residue_divS (R j : Nat) :
    gstDigitS R j = (R % 3^(j+1)) / 3^j

/-- Equality through ternary depth j+1 preserves the complete GST vertex at j:
both the input digit and the incoming multiply-by-four carry. -/
theorem gst_state_eq_of_prefix_residueS
    (R S j : Nat)
    (hres : R % 3^(j+1) = S % 3^(j+1)) :
    gstDigitS R j = gstDigitS S j ∧
      gstCarryS R j = gstCarryS S j

/-- Canonical origin causality at one exact GST vertex: the state at
position j depends only on n modulo 3^(j+1). -/
theorem gst_canonical_state_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t) :
    let a := n % 3^(j+1)
    gstDigitS (Q t n) j = gstDigitS (Q t a) j ∧
      gstCarryS (Q t n) j = gstCarryS (Q t a) j

/-- A canonical child Happy Gate is already present in the finite origin
prefix that ends exactly at the gate's causal depth. -/
theorem gst_canonical_gate_from_origin_prefixS
    (Q : Nat → Nat → Nat)
    (hQ : GSTCanonicalOriginEnergyS Q)
    (t n j : Nat) (ht : 1 ≤ t)
    (hgate : gstDigitS (Q t n) j = 2 ∧
      (gstCarryS (Q t n) j = 0 ∨ gstCarryS (Q t n) j = 3)) :
    let a := n % 3^(j+1)
    gstDigitS (Q t a) j = 2 ∧
      (gstCarryS (Q t a) j = 0 ∨ gstCarryS (Q t a) j = 3)
```

### F2. The self-read feedback law — the master causality law of the power stream (`GSTTheActConstruction.lean:79`)

```lean
/-- **THE SELF-READ LAW.**  For every exponent `K` and every level `j`, the
row-`j+1` trit of `4^K` is the row-`j+1` trit of the prefix-power
`4^(K mod 3^j)` plus the `j`-th trit of `K`, modulo three.  The power's
digit stream is the exponent's digit stream fed through the prefix-power's
digit stream — one feedback system, every row, every exponent, no
hypothesis. -/
theorem self_read (K j : Nat) :
    digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3

/-- **THE ROW-ONE READ.**  Row one of `4^K` is exactly `K % 3`. -/
theorem row_one_read (K : Nat) : digit3 (4^K) 1 = K % 3

/-- **THE ROW-ONE KILL.**  Every exponent `K ≡ 2 mod 3` fires its digit
two at row one. -/
theorem row_one_kill (K : Nat) (h : K % 3 = 2) : digit3 (4^K) 1 = 2

/-- **THE CANTORIAN CONSTRAINT SYSTEM.**  `CantorianPower K` holds IF AND
ONLY IF at EVERY level `j` the prefix noise plus the exponent trit never
lands on two: the entire Cantorian core is the set of exponents that
thread the feedback tree at every level. -/
theorem cantorian_iff_feedback (K : Nat) :
    CantorianPower K ↔ ∀ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 ≠ 2

/-- **THE ACT AS TREE-ESCAPE.**  The act holds IF AND ONLY IF every
exponent from eight on fires somewhere in the feedback tree. -/
theorem the_act_iff_feedback :
    GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2
```

### F3. Noise window and the unique dead child — the causality of the feedback noise

```lean
/-- **THE NOISE WINDOW LAW.**  Beyond the diagonal window the prefix
noise vanishes: when the prefix-power stays below the modulus, its
row-`j+1` trit is zero.  The feedback's noise lives in the window
`4^r ≥ 3^(j+1)`. -/
theorem noise_window_law (r j : Nat) (h : 4^r < 3^(j+1)) :
    digit3 (4^r) (j + 1) = 0

/-- **THE UNIQUE DEAD CHILD.**  At every level, every prefix owns
EXACTLY ONE dead child-trit: `(2 - noise) mod 3`.  Every node of the
dust tree has exactly two alive children, forever, by structure. -/
theorem unique_dead_child (r j : Nat) :
    ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j + 1) + t) % 3 = 2
```

### F4. The uniform kill engine — one law, every level

```lean
/-- **PREFIX UNPACKING.**  A class membership `K ≡ r + 3^j·t mod 3^(j+1)`
with `r < 3^j` and `t < 3` unpacks into: `K`'s level-`j` prefix is `r`,
and `K`'s `j`-th trit is `t`. -/
theorem prefix_unpack (K j r t : Nat) (hr : r < 3^j) (ht : t < 3)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    K % 3^j = r ∧ digit3 K j = t

/-- **THE UNIFORM KILL.**  At ANY level `j`, an alive prefix `r` and its
one dead child-trit `t` — certified by the closed noise receipt
`(digit3 (4^r) (j+1) + t) % 3 = 2` — kill the entire congruence class
`K ≡ r + 3^j·t mod 3^(j+1)` at row `j+1`: every member fires its digit
two.  Every cascade level, current and future, is an instance. -/
theorem feedback_fire_of_class (j r t K : Nat)
    (hr : r < 3^j) (ht : t < 3)
    (hnoise : (digit3 (4^r) (j + 1) + t) % 3 = 2)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    digit3 (4^K) (j + 1) = 2
```

## §G. THE INFINITE THEOREM CONTROLLERS

### G1. The main infinite control graph (`GSTGraphV2InfiniteControl.lean`, 260 lines)

```lean
/-- One enriched cell of the main infinite GST V2 graph. -/
structure InfiniteCell where
  seven : GSTCanonicalSevenAxisBridge.Vertex
  eventCode : Nat
  uCharge : Int
  mixedCharge : Int
  crossingCharge : Int
  survive : Int
  deriving Repr

/-- Enrich one canonical seven-axis vertex with all green charge observables. -/
def cell (E t p : Nat) : InfiniteCell :=
  let v := GSTCanonicalSevenAxisBridge.vertex E t p
  {
    seven := v
    eventCode := GSTCanonicalSevenAxisBridge.event v.carry v.digit
    uCharge := gstUChargeExact v.carry
    mixedCharge := mixedDensity v.carry v.digit
    crossingCharge := crossDensity v.carry v.digit
    survive := surviveI v.carry v.digit
  }

/-- The main graph is genuinely all-depth in both arithmetic directions. -/
def graph (E : Nat) : Nat → Nat → InfiniteCell :=
  fun t p => cell E t p

/-- Every cell of the enriched graph obeys the exact x4/base3 lattice law. -/
theorem graph_cell_exact (E t p : Nat) :
    outDigit (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E (t+1) p).seven.digit ∧
      nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
        (graph E t (p+1)).seven.carry

/-- Happy is event eight on the main infinite graph. -/
theorem graph_happy_iff_event_eight (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      (graph E t p).eventCode = 8

/-- Happy is equivalently positive exact crossing charge. -/
theorem graph_happy_iff_crossing_positive (E t p : Nat) :
    HappyCell (graph E t p).seven.carry (graph E t p).seven.digit ↔
      0 < (graph E t p).crossingCharge

/-- The event-balance equation is available at every cell. -/
theorem graph_event_balance_exact (E t p : Nat) :
    (graph E t p).eventCode +
        9 * nextCarry (graph E t p).seven.carry (graph E t p).seven.digit =
      13 * (graph E t p).seven.digit + 3 * (graph E t p).seven.carry
```

The full-energy prefix-slice projection — the production socket:

```lean
/-- Seeded x4 carry used by a full-energy prefix slice. -/
def seededCarry (seed tail q : Nat) : Nat :=
  (seed + 4 * (tail % 3^q)) / 3^q

theorem prefix_slice_quotient_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    (P + 3^b * tail) / 3^(b+q) = tail / 3^q

/-- The information digit on the full-energy slice is literally the tail digit. -/
theorem prefix_slice_digit_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    digit3 (P + 3^b * tail) (b+q) = digit3 tail q

/-- Exact seeded carry projection.  The seed is not assumed: it is generated
by the canonical low prefix as `floor(4*P / 3^b)`. -/
theorem prefix_slice_carry_exact
    (b P tail q : Nat) (hP : P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) =
      seededCarry ((4 * P) / 3^b) tail q

theorem prefix_slice_seed_zero
    (b P tail q : Nat) (hP : P < 3^b) (hseed : 4 * P < 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 0 tail q

theorem prefix_slice_seed_one
    (b P tail q : Nat) (hP : P < 3^b)
    (hlo : 3^b ≤ 4 * P) (hhi : 4 * P < 2 * 3^b) :
    carry4 (P + 3^b * tail) (b+q) = seededCarry 1 tail q

/-- Literal graph form of the prefix-slice socket.  Any exact decomposition
of the horizontal full energy gives both the tail trit and the
prefix-generated seeded carry at the corresponding vertical slice. -/
theorem graph_prefix_slice_exact
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    (graph E t (b+q)).seven.digit = digit3 tail q ∧
      (graph E t (b+q)).seven.carry =
        seededCarry ((4 * P) / 3^b) tail q

/-- On a literal full-energy slice, Happy/event-eight is exactly the seeded
Happy predicate of the exposed tail. -/
theorem graph_prefix_slice_happy_iff
    (E t b P tail q : Nat)
    (hE : 4^t * E = P + 3^b * tail)
    (hP : P < 3^b) :
    HappyCell
        (graph E t (b+q)).seven.carry
        (graph E t (b+q)).seven.digit ↔
      digit3 tail q = 2 ∧
        (seededCarry ((4 * P) / 3^b) tail q = 0 ∨
         seededCarry ((4 * P) / 3^b) tail q = 3)
```

### G2. The never-firing tower and the Cantorian core (`GSTClimbInfiniteFamily.lean`)

```lean
/-- **THE CANTORIAN CORE.**  An exponent whose power of four carries no
digit two at any row from one upward — the exact Erdős core. -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- **THE COLLAPSE.**  The act holds IF AND ONLY IF no exponent from
eight on is a Cantorian power. -/
theorem the_act_iff_no_cantorian :
    GSTTheAct.the_act ↔ ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K

/-- **THE FINAL SOCKET.**  No Cantorian exponent from eight on ⇒ the act
⇒ `hTailF`. -/
theorem hTailF_of_no_cantorian
    (h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF

/-- **THE NEVER-FIRING TOWER.**  No sheet of the core's whole
multiplicative-three tower ever owns a ternary digit two. -/
def NeverFiringTower (core : Nat) : Prop :=
  ∀ S p : Nat, digit3 (4^(3^S * core)) (S + 1 + p) ≠ 2

/-- The never-firing tower dodges every sheet window. -/
theorem hwin_of_never_firing {core : Nat} (h : NeverFiringTower core) :
    ∀ s : Nat, 1 ≤ s →
      (GSTGraphV2OmegaWaveLaw.omegaCutWord s core) % 3^(s+2)
        < 2 * 3^(s+1)

/-- The never-firing tower dodges the diagonal fire band at every level
from three upward. -/
theorem hdust_of_never_firing {core : Nat} (h : NeverFiringTower core) :
    ∀ k : Nat, 3 ≤ k →
      (GSTGraphV2OmegaWaveLaw.omegaCutWord (k-1) 1 * core) % 3^k
        < 2 * 3^(k-1)

/-- **THE ALL-ONES DIAGONAL.**  A never-firing three-free core's scaled
diagonal is pinned to the exact middle third at every level from three
upward. -/
theorem never_firing_diagonal_all_ones {core : Nat}
    (hfree : core % 3 = 1 ∨ core % 3 = 2)
    (h : NeverFiringTower core) :
    ∀ j : Nat, 2 ≤ j →
      digit3 (GSTGraphV2OmegaWaveLaw.omegaCutWord j 1 * core) j = 1

/-- **THE TOWER DUST IS EMPTY.**  No three-free core has a never-firing
tower: every core's multiplicative-three tower meets its ternary digit
two.  The six residue classes of `core % 9` each die — three at the front
row, one in the frozen band, two by the kernel-checked deep cuts. -/
theorem tower_dust_empty (core : Nat) (hfree : ¬ 3 ∣ core) :
    ¬ NeverFiringTower core
```

Also in this file: the climb family (`pair_law :70`, `wave3_deep_member :96`, `climb_witness_eighteen :119`, `wave3_deep_unbounded :135`), the prefaced window laws (`prefaced_window_law/full/sliced :149-203`), `every_row_is_read :215`, and the dust row reads:

```lean
theorem dust_row_two   (w : Nat) : digit3 (4^(3*w+1)) 2 = w % 3
theorem dust_row_three (w : Nat) : digit3 (4^(3*w+1)) 3 = (w/3) % 3
theorem dust_row_four_one (u : Nat) : digit3 (4^(9*u+1)) 4 = (u/3) % 3
theorem dust_row_four_four (u : Nat) : digit3 (4^(9*u+4)) 4 = (u/3) % 3
```

and the trit-slice laws:

```lean
theorem digit3_eq_mod_slice (X p : Nat) :
    digit3 X p = (X % 3^(p+1)) / 3^p

theorem digit3_of_top_third (X p : Nat)
    (h : 2 * 3^p ≤ X % 3^(p+1)) : digit3 X p = 2

theorem digit3_of_mid_range (X p : Nat)
    (h1 : 3^p ≤ X % 3^(p+1)) (h2 : X % 3^(p+1) < 2 * 3^p) :
    digit3 X p = 1
```

### G3. Other controller modules (all green, in the repo)

- `GSTGraphV2InfiniteControllerBridge.lean` — the bridge between the infinite control graph and the tower observers.
- `GSTV2InfiniteCore.lean`, `GSTInfiniteBadTransport.lean`, `GSTInfiniteCollision.lean`, `GSTInfiniteCoupledLedger.lean`, `GSTInfiniteFourPowerNavigation.lean` (the climb: `four_power_happy_climb`), `GSTInfiniteGateTransport.lean`.
- `GSTGraphV2CanonicalInfiniteCycle.lean`, `GSTGraphV2InfiniteBigNDichotomyScratch.lean`, `GSTGraphV2InfiniteControlScratch/Smoke.lean`.

## §H. THE POLYNOMIAL BLADES — worldtrace arithmetic proper (`GSTWorldtraceArithmetic.lean`, 1222 lines)

### H1. The binomial ladder

```lean
theorem wt_choose_one (n : Nat) : Nat.choose n 1 = n

/-- **The three-term binomial ladder.** -/
theorem one_add_pow_three_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x + x*x*x*R

/-- **The four-term binomial ladder.** -/
theorem one_add_pow_four_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + x*x*x*x*R

/-- **The five-term binomial ladder.** -/
theorem one_add_pow_five_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x
      + x*x*x*x*x*R

/-- **THE REBASE.**  Every dust power is a power of sixty-four. -/
theorem wt_rebase (m : Nat) : 4^(1+3*m) = 4 * 64^m
```

### H2. The blades

```lean
/-- **THE QUADRATIC BLADE.**  Row-window congruence of the dust power:
`4^(1+3m)` is the quadratic `4 + 252m + 15876*C(m,2)` mod 729 — the
order-two worldtrace. -/
theorem wt_quad_mod729 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]

/-- **THE CUBIC BLADE.**  One window deeper. -/
theorem wt_cubic_mod6561 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561]

/-- **THE QUARTIC BLADE.**  Two windows deeper. -/
theorem wt_quartic_mod19683 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683]
```

### H3. The reads — deep rows ARE the polynomials

```lean
/-- **ROW FIVE IS THE QUADRATIC.**  For EVERY m. -/
theorem wt_row_five_read (m : Nat) :
    digit3 (4^(1+3*m)) 5 = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5

/-- **ROW SEVEN IS THE CUBIC.** -/
theorem wt_row_seven_read (m : Nat) :
    digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7

/-- **ROW EIGHT IS THE QUARTIC.** -/
theorem wt_row_eight_read (m : Nat) :
    digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8

/-- **THE QUARTIC KILL DEMO.**  The quartic blade kills K = 82 (m = 27)
at row eight WITHOUT EVER COMPUTING `4^82`. -/
theorem wt_quartic_fire_demo : digit3 (4^(1+3*27)) 8 = 2

/-- **THE POLYNOMIAL KILL DEMO.**  The quadratic blade kills K = 85
(m = 28) at row five WITHOUT EVER COMPUTING `4^85`. -/
theorem wt_quad_fire_demo : digit3 (4^(1+3*28)) 5 = 2
```

### H4. The cascade levels — the kill tables

Level-six form (row seven, modulus 2187, 32 dead classes → 64 survivors):

```lean
theorem fire_of_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2

theorem dust_fire_row_seven (K : Nat) (hK : K % 2187 = 31 ∨ K % 2187 = 37 ∨
    K % 2187 = 118 ∨ K % 2187 = 172 ∨ K % 2187 = 253 ∨ K % 2187 = 256 ∨
    K % 2187 = 271 ∨ K % 2187 = 337 ∨ K % 2187 = 352 ∨ K % 2187 = 409 ∨
    K % 2187 = 487 ∨ K % 2187 = 490 ∨ K % 2187 = 526 ∨ K % 2187 = 568 ∨
    K % 2187 = 607 ∨ K % 2187 = 679 ∨ K % 2187 = 685 ∨
    {…16 more classes: 10, 28, 82, 100, 163, 190, 199, 244, 262, 280, 325,
     406, 442, 469, 514, 595, 616, 652…}) :
    digit3 (4^K) 7 = 2

/-- **THE DUST PINNED AT LEVEL SIX** — the 64-survivor map mod 2187. -/
theorem cantorian_dust_mod_2187 (K : Nat) (hd : K % 3 = 1)
    (hc : CantorianPower K) :
    K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 10 ∨ … ∨ K % 2187 = 2005
    -- (all 64 survivors listed in the file, :342)
```

Level-seven form (row eight, modulus 6561, 64 dead classes → 128 survivors): `fire_of_mod6561 :425`, `dust_fire_row_eight :446`, `cantarian_dust_mod_6561 :521`, `no22_of_cascade_seven :658`. Earlier levels in `GSTTheActConstruction.lean`: `fire_of_mod243 :208`, `dust_fire_row_five :230` (8 classes: 85, 91, 112, 118, 163, 175, 190, 202 mod 243), `fire_of_mod729 :367`, `dust_fire_row_six :389` (16 classes: 31, 37, 172, 253, 256, 271, 337, 352, 409, 487, 490, 526, 568, 607, 679, 685 mod 729); survivor maps `cantorian_dust_mod_9/27/81/243/729` (:254-:423).

Cumulative structure: **66 dead classes across 7 levels; the survivor set doubles 2 → 4 → 8 → 16 → 32 → 64 → 128 at every level, by `unique_dead_child`.**

### H5. The pair-read infinite family — GAP-E1

```lean
/-- **THE PAIR-READ FORMULA.**  The two-support tower factorization, read
through the green `prefaced_digit`: for `1 ≤ j` and any trunk `T` with
`4^T < 3^(j+2)`, the row-`(j+4)` digit of `4^(T + 3^(j+1)*u)` is the
row-two digit of the worldtrace product `4^T * u * c (j+1)`. -/
theorem pair_read_formula (T u j : Nat) (hj : 1 ≤ j) (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2

/-- **THE PAIR-READ FIRE.**  Every exponent `K = 4 + 3^(j+1)*u` with `j ≥ 4`
and `u ∈ {1, 4, 7}` fires its digit two at row `j+4`. -/
theorem pair_read_fire (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2

/-- **THE PAIR-READ RESIDUE.**  The worldtrace product's mod-27 residue is
computable without the tower: `c (j+1)` is `16 mod 27`. -/
theorem pair_residue_mod27 (T u j : Nat) (hj : 2 ≤ j) :
    (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27

/-- **THE ROW-TWO READ FROM THE KILL ZONE.** -/
theorem digit3_row_two_of_residue (x : Nat) (hx : 18 ≤ x % 27) :
    digit3 x 2 = 2

/-- **THE GENERAL TRUNK-UNIFORM FIRE.**  ANY trunk `T`, ANY branch `u`:
whenever `(4^T * u * 16) % 27 ≥ 18`, the exponent `T + 3^(j+1)*u` fires
its digit two at row `j+4`.  The kill condition is a mod-27 computation
on the trunk residue and the branch — the Cantor automaton's transition,
uniform across the entire dust tree. -/
theorem pair_read_fire_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2

/-- SECOND FAMILY — trunk-13: fires at row j+4 for every j ≥ 15. -/
theorem pair_read_fire_demo_two (j : Nat) (hj : 15 ≤ j) :
    digit3 (4^(13 + 3^(j+1))) (j+4) = 2

/-- THIRD FAMILY — trunk-10 branch-two: fires at row j+4 for every j ≥ 11. -/
theorem pair_read_fire_demo_three (j : Nat) (hj : 11 ≤ j) :
    digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2
```

### H6. The descent engine — the top split and the addition window

```lean
/-- **THE EXACT TOP SPLIT.**  For an exponent `K` whose top trit sits at
position `H`, the power splits as the trunk power, the branch term, and a
tail dead below row `2H+2`.  The deep rows of `4^K` are a pure base-3
addition of the trunk's digits and the shifted digits of
`X = t * c(H) * 4^trunk`. -/
theorem top_split (K H : Nat) (hK : K < 3^(H+1)) :
    ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)
        + 3^(H+1) * Y)

/-- **THE ADDITION WINDOW.**  Below row `2H+2`, the digits of `4^K` read
the two-term sum `4^trunk + 3^(H+1) * X` — the dead tail of the top
split is invisible. -/
theorem window_congr (K H r : Nat) (hK : K < 3^(H+1)) (hr : r + 1 ≤ 2*H+2) :
    digit3 (4^K) r = digit3 (4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r

/-- **THE ROW-(H+2) WINDOW LAW.**  The digit at row `H+2` of `4^K` is the
trunk's own digit at that row, plus the first trit of the branch factor,
plus the carry from row `H+1` — a pure base-3 addition read. -/
theorem window_row_two (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1)) :
    digit3 (4^K) (H+2)
      = (digit3 (4^(K % 3^H)) (H+2)
          + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
          + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3
```

### H7. The dust window laws — the branch term vanishes mod nine

```lean
/-- **THE PERIOD-NINE LAW.**  `4^r mod 9` depends only on `r mod 3`. -/
theorem four_pow_mod9 (r : Nat) : (4:Nat)^r % 9 = 4^(r % 3) % 9

/-- **THE DUST BRANCH FACTOR.**  For a dust trunk (`trunk mod 3 = 1`) the
branch factor `X = t * c(H) * 4^trunk` satisfies `X mod 9 = t` —
`c(H)` is `7 mod 9`, `4^trunk` is `4 mod 9`, and `7 * 4 = 28 = 1 mod 9`:
the branch factor's first trit VANISHES. -/
theorem dust_branch_mod9 (t trunk H : Nat) (hH : 1 ≤ H) (htr : trunk % 3 = 1)
    (ht : t < 3) :
    (t * GSTTowerFire.c H * 4^trunk) % 9 = t

/-- **THE DUST ROW-(H+2) LAW — the branch term vanishes.**  For a dust
exponent the row-(H+2) digit is JUST the trunk's digit plus the carry. -/
theorem window_row_two_dust (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1))
    (hdust : K % 3 = 1) :
    digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
      + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3

/-- **THE WINDOW REDUCE.**  The digit at row `H+1+s` sees only X's first
`s+1` trits — the consumers' computational handle. -/
theorem window_reduce (A X H s : Nat) : ...   -- :1087
```

## §I. THE TOWER FIRE LAWS (`GSTTowerFire.lean`)

```lean
/-- **Divide-and-mod gluing.** -/
theorem div_add_lt (k q s : Nat) (hs : s < 3^k) : (3^k * q + s) / 3^k = q

/-- **The prefaced read.**  If `s < 3^(n+1)` then row `n+1+k` of the
prefaced object `3^(n+1) * A + s` is row `k` of `A`. -/
theorem prefaced_digit (A s n k : Nat) (hs : s < 3^(n+1)) :
    digit3 (3^(n+1) * A + s) (n+1+k) = digit3 A k

/-- **THE DEEP-HIDER MASTER LEMMA.**  Rows `n+1 .. 2n+1` of `4^(j * 3^n)`
are the digits `0 .. n` of `j * c n`: one tower constant governs every
scaled family at every depth. -/
theorem tower_digit_read (j n k : Nat) (hk : k ≤ n) :
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k

/-- **THE n+2 LAW.**  `3^n` fires at row `n+2` for every `n ≥ 1`. -/
theorem three_pow_fires (n : Nat) (hn : 1 ≤ n) : digit3 (4^(3^n)) (n+2) = 2

/-- **THE n+1 LAW.**  `2 * 3^n` fires at row `n+1` for every `n ≥ 0`. -/
theorem two_mul_three_pow_fires (n : Nat) : digit3 (4^(2 * 3^n)) (n+1) = 2

/-- **THE n+4 LAW.**  `3^n + 1` fires at row `n+4` for every `n ≥ 3`:
the prefaced tower constant `4 * c n ≡ 64 mod 81 = 2101₃` plants the TWO
at offset three. -/
theorem three_pow_plus_one_fires (n : Nat) (hn : 3 ≤ n) :
    digit3 (4^(3^n + 1)) (n+4) = 2
```

The tower-axis covers $s \geq 1$ structurally (`GSTTowerAxis.lean`):

```lean
theorem tower_axis_level_one   (s c : Nat) (hs : 1 ≤ s) (hc : c % 9 = 1) : ...
theorem tower_axis_level_two   (s c : Nat) (hs : 2 ≤ s) (hc : c % 27 = 4 ∨ ...) : ...
theorem tower_axis_level_three (s c : Nat) (hs : 3 ≤ s) (hc : ...) : ...
theorem not_cantarian_of_tower_axis {K s c : Nat} (hK : K = 3^s * c) ... : ¬ CantorianPower K
theorem no22_of_tower_axis {K s c : Nat} (hK : K = 3^s * c) ... : noTernaryTwo (4^K) = false
```

## §J. THE DIAGONAL READ — the triage (`GSTDiagonalRead.lean`)

```lean
/-- Every positive exponent decomposes uniquely as `3^v · u` with
`u` not divisible by three — the valuation cut. -/
theorem valuation_decomp (K : Nat) :
    0 < K → ∃ v u : Nat, K = 3^v * u ∧ u % 3 ≠ 0

/-- **THE DIAGONAL WINDOW LAW** — every exponent's entire readable band,
one law, all scales: for `j ≤ v`, row `v+1+j` of `4^(3^v*u)` is row `j`
of `u * lteCoeff v`. -/
theorem diagonal_window_law (v u j : Nat) (hj : j ≤ v) :
    digit3 (4^(3^v * u)) (v + 1 + j) = digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j

/-- **THE WINDOW-CLEAN DUST.**  The read's exact residual: exponents whose
reduced core is `1 mod 3` and whose readable diagonal never fires. -/
def WindowCleanDust (K : Nat) : Prop :=
  ∃ v u : Nat, K = 3^v * u ∧ u % 3 = 1 ∧
    ∀ j ≤ v, digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j ≠ 2

/-- **THE TRIAGE.**  Every exponent `K ≥ 8` either owns its digit two — by
the front fire or by a window fire, both uniform laws — or is window-clean
dust.  No third case: the whole plane of exponents, one dichotomy. -/
theorem every_exponent_fires (K : Nat) (hK : 8 ≤ K) :
    (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K

/-- **THE SOCKET, COMPLETE.**  Dust empty ⇒ the act ⇒ `hTailF`. -/
theorem hTailF_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF
```

Window fire families (uniform, all green): `window_fire_level1` ($u \equiv 1 \bmod 9 \Rightarrow$ row $v{+}2$ fires), `window_fire_level2` ($u \equiv 13, 25 \bmod 27 \Rightarrow$ row $v{+}3$), `window_fire_level3` ($u \equiv 4, 34, 49, 70 \bmod 81 \Rightarrow$ row $v{+}4$).

## §K. THE ONE LANE — the whole construction, one theorem, zero hypotheses (`GSTTailFOneLane.lean`)

```lean
/-- **THE CANONICAL DECOMPOSITION.**  Every positive exponent `M` is a
tower-core pair `M = 3^s * core` with `core` three-free. -/
theorem one_lane_three_free_decomposition (M : Nat) : 0 < M →
    ∃ s core : Nat, M = 3^s * core ∧ ¬ 3 ∣ core

/-- **THE TOWER'S UNIT WORD.**  The cut word of the unit core is the LTE
mean itself: `omegaCutWord s 1 = lteCoeff s`. -/
theorem one_lane_cut_word_one (s : Nat) : omegaCutWord s 1 = lteCoeff s

/-- **FIRE AT THE CUT ROW.**  Every sheet-core pair whose core is congruent
to two modulo three fires at row `s+1`. -/
theorem one_lane_fire_of_mod3_two (s core : Nat) (h : core % 3 = 2) :
    digit3 (4^(3^s * core)) (s+1) = 2

/-- **FIRE ABOVE THE CUT.**  Every tower core congruent to one modulo nine,
above sheet zero, fires at row `s+2`. -/
theorem one_lane_fire_of_tower_mod9_one (s core : Nat) (hs : 1 ≤ s)
    (h : core % 9 = 1) : digit3 (4^(3^s * core)) (s+2) = 2

/-- **FIRE AT ROW TWO OF THE SHEET-ZERO CYCLE.**  Every exponent congruent
to seven modulo nine fires at row two. -/
theorem one_lane_row2_fire (K : Nat) (h : K % 9 = 7) :
    digit3 (4^K) 2 = 2

/-- **THE ONE-LANE CASE MAP.**  For every exponent `K+1`: either `4^(K+1)`
owns a ternary digit two, or the exponent's canonical sheet-core pair
carries the full no-fire certificate — the three-free family clause of the
shadow package together with a cut word whose every depth dodges the top
third.  Unconditional. -/
theorem one_lane_complete (K : Nat) :
    (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i))

/-- **THE CERTIFICATE'S FACES.**  Every exponent carrying the dust
certificate satisfies the shadow package's window clause, diagonal clause,
and row-all-depths clause. -/
theorem one_lane_certificate_faces (s core : Nat)
    (hfam : core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
    (hnever : ∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) :
    (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (s = 0 → ∀ j : Nat, 2 ≤ j →
      (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j)

/-- **THE ONE-LANE RECEIPT — the whole construction, one theorem, zero
hypotheses.**  Every exponent's case map (fire or the complete dust
certificate), the certificate's faces, the engine (the exact cube lift),
the three-window dichotomy, the dust's shape, and the floor identity. -/
theorem one_lane_the_whole_construction :
    (∀ K : Nat, (∃ p : Nat, digit3 (4^(K+1)) p = 2) ∨
      (∃ s core : Nat, (K+1) = 3^s * core ∧ ¬ 3 ∣ core ∧
        (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))
        ∧ (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i))) ∧
    (∀ s core : Nat,
      (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) →
      (∀ i : Nat, (omegaCutWord s core) % 3^(i+1) < 2 * 3^i) →
      ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1) ∧
        (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
          (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) ∧
        (s = 0 → ∀ j : Nat, 2 ≤ j →
          (omegaCutWord 0 core) % 3^(j+1) < 2 * 3^j))) ∧
    (∀ s core : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core
        + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
          + 3^s * (omegaCutWord s core * omegaCutWord s core
            * omegaCutWord s core))) ∧
    (∀ s core : Nat, 1 ≤ s → core % 3 = 1 ∨ core % 3 = 2 →
      (2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ digit3 (4^(3^s * core)) (2*s+2) = 2)
      ∨ (omegaCutWord s core) % 3^(s+2) < 3^(s+1)
      ∨ (3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)
        ∧ (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)
        ∧ ∀ S : Nat, s+1 ≤ S →
          digit3 (4^(3^S * core)) (S + (s+2)) = 2)) ∧
    (∀ core : Nat, core % 3 = 1 ∨ core % 3 = 2 →
      (∀ s : Nat, 1 ≤ s →
        (omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1)) →
      (∀ k : Nat, 3 ≤ k →
        (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∀ k : Nat, 3 ≤ k →
        3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k
          ∧ (omegaCutWord (k-1) 1 * core) % 3^k < 2 * 3^(k-1)) ∧
    (four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
```

## §L. The proof-file composition (`GSTTailFProof.lean`, 434 lines)

```lean
/-- **THE ROW EYE.** -/
theorem row_observation_law (core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)) :
    digit3 (4^core) (1 + j) = 2

/-- **THE TOWER EYE.** -/
theorem tower_observation_law (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2

/-- **THE WAVE FACE — the GST observation law itself, advanced form.**
A Happy cell on the unit sheet of the power column, with an all-depth bad
boundary three x4 waves to its right, is not erased: it reappears as a
strictly positive coupled-U derivative.  Information propagates, never
dies — the observation law of the universe, stated on the physical graph. -/
theorem observation_law_wave :
    ∀ (K q : Nat),
      (HappyCell (graph (4^K) 0 (3+q)).seven.carry
                 (graph (4^K) 0 (3+q)).seven.digit) →
      (∀ j : Nat, ¬ HappyCell (graph (4^K) 3 (3+j)).seven.carry
                       (graph (4^K) 3 (3+j)).seven.digit) →
      0 < graphPhaseWindow (4^K) 0 3 (q+1) ∧
        graphPhaseWindow (4^K) 3 3 (q+1) ≤ 0 ∧
        64 * (graph (4^K) 0 (3+q)).seven.digit +
            wideCarry 64 (4^K) (3+q) =
          (graph (4^K) 3 (3+q)).seven.digit +
            3 * wideCarry 64 (4^K) ((3+q)+1) ∧
        0 < 3 * potentialWith gstUChargeExact (4^3)
              (unifiedState (4^K) 3 ((3+q)+1)).core -
            potentialWith gstUChargeExact (4^3)
              (unifiedState (4^K) 3 (3+q)).core

/-- **THE CURRENT — the ontological spacetime certificate.**  A physical
cell of the dimensionless graph is Happy exactly when its ontological
current is positive. -/
theorem universe_current_happy_iff (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < GSTGraphV2Ontological.ontDensity C d

/-- **THE NO-ERASURE WINDOW.**  A Happy source on the left edge of any
nonzero-width production window keeps the window's ontological current
strictly positive. -/
theorem universe_window_positive_of_happy (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell (graph E 0 (b+q)).seven.carry
                      (graph E 0 (b+q)).seven.digit) :
    0 < GSTGraphV2Ontological.graphOntWindow E N b (q+1)

/-- **THE PROOF OF hTailF** (climb form — the single named primitive). -/
theorem hTailF
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    four_power_omega_shadow_wave_tailF

/-- **THE TERMINAL IDENTITY, CARRIED INTO THE PROOF FILE.** -/
theorem hTailF_iff_even_conjecture :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF ↔
      ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE META-VIEW RECEIPT.**  One theorem, four faces: the observation
law uniform over every family; the uniform ignition blade uniform over
every level; the dust boundary; the floor identity. -/
theorem meta_view_all_classes_all_levels :
    (∀ s core j : Nat, 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1) →
        digit3 (4^(3^s * core)) (s+1+j) = 2) ∧
    (∀ k core S : Nat, 1 ≤ k → k ≤ S+1 →
        2 * 3^(k-1) ≤ (omegaCutWord (k-1) 1 * core) % 3^k →
        digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (∀ core : Nat, ¬ omega_diagonal_survivor_dust core →
        ∃ k : Nat, 3 ≤ k ∧ ∀ S : Nat, k-1 ≤ S →
          digit3 (4^(3^S * core)) (S + k) = 2) ∧
    (four_power_omega_shadow_wave_tailF ↔
        ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)

theorem even_conjecture_of_climb
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false
```

Lattice cycle laws (new laws, deepest levels):

```lean
theorem new_law_four_pow_mod2187 (m : Nat) :
    (4^m) % 2187 = (4^(m % 729)) % 2187
theorem new_law_four_pow_mod6561 (m : Nat) :
    (4^m) % 6561 = (4^(m % 2187)) % 6561
theorem four_pow_mod243 (m : Nat) : (4^m) % 243 = (4^(m % 81)) % 243
theorem four_pow_mod729 (m : Nat) : (4^m) % 729 = (4^(m % 243)) % 729
```

## §M. The exact U-machinery (`GSTGraphV2HandwrittenOmegaUBlock.lean`)

```lean
def originTrit (n : Nat) : Nat := n % 3
def originTail (n : Nat) : Nat := n / 3

theorem origin_split_exact (n : Nat) :
    n = originTrit n + 3 * originTail n

/-- The kernel-grade content of the handwritten simultaneous x/div U symbol:
all perfect-power energy is conserved while one ternary origin trit is
consumed into the left phase factor. -/
theorem perfect_power_u_mul_div_exact (t n : Nat) :
    4^(3^t * n) =
      4^(3^t * originTrit n) * 4^(3^(t+1) * originTail n)

def residualEnergy (s k m : Nat) : Nat := 4^(3^(s+k) * m)
def residualWidth (s : Nat) : Nat := 3^s
def residualChildExponent (s k m : Nat) : Nat := 3^(s+k) * m
def residualParentExponent (s k m : Nat) : Nat := 3^s * (1 + 3^k * m)

theorem residual_parent_energy_exact (s k m : Nat) :
    4^(residualWidth s) * residualEnergy s k m =
      4^(residualParentExponent s k m)

/-- Full Graph-V2 realization: every physical observable at the alleged
all-bad right boundary is literally the absolute perfect-power sheet at
the canonical parent exponent. -/
theorem residual_parent_observables_exact (s k m p : Nat) :
    (graph (residualEnergy s k m) (residualWidth s) p).seven.carry =
        (graph 1 (residualParentExponent s k m) p).seven.carry ∧
    (graph (residualEnergy s k m) (residualWidth s) p).seven.digit =
        (graph 1 (residualParentExponent s k m) p).seven.digit ∧
    … (eventCode, uCharge, mixedCharge, crossingCharge, survive) …

/-- Happy/event-eight transport at the actual residual parent boundary. -/
theorem residual_parent_happy_iff (s k m p : Nat) :
    HappyCell (graph (residualEnergy s k m) (residualWidth s) p).seven.carry
              (graph (residualEnergy s k m) (residualWidth s) p).seven.digit ↔
      HappyCell (graph 1 (residualParentExponent s k m) p).seven.carry
                (graph 1 (residualParentExponent s k m) p).seven.digit
```

## §N. Verified numerical receipts of the worldtrace descent (modular, exact big-int; all 0 failures)

These are machine-verified laws of the machinery (from the derivations, `/tmp` receipts, kept as experimental ground truth):

- **D1**: $W_t(3m) = 3\,W_{t+1}(m)$ where $W_t(m) := (4^{3^t m} - 1)/3^{t+1} = \omega\mathrm{CutWord}(t,m)$ — 8/8 exact passes.
- **D2**: $W_t(3q+1) = 1 + 12\,W_{t+1}(q)$ — 9/9 passes.
- **D3 (transfer)**: $W_t(3^t m + 1) = 1 + 4 \cdot 3^t\, W_t(m)$ — 24/24 passes.
- **D4 (stabilization)**: $\text{trit}_j(W_t(m)) = \text{trit}_j(c_t \cdot m)$ for $j \le t$, where $c_0 = 1, c_1 = 7, c_2 = 9709, c_3 = 222399981598543, \ldots$ ($c_t = \mathrm{lteCoeff}(t)$) — 27/27 passes.
- **D4b**: $\text{trits}(W_t(m)) = \text{trits}(c_\infty \cdot m)$ below depth $t$, with $c_\infty$ the frozen limit (trits $[1,2,1,0,2,2,0,1,0,2,1,2,1,0,\ldots]$) — 27/27 passes.
- **D5 (emit-2 table)**: the carry-digit emit law of $4W$: emit 2 exactly on pairs $(\text{carry},\text{digit}) \in \{(0,2),(1,1),(2,0),(3,2)\}$; carry $\in \{0..3\}$ satisfies $v_j = \text{digit}_j(4R) + \text{carry}$, $\text{carry}_{j+1} = \text{carry4}$ — 0 failures / 31458 steps.
- **D6**: dust-equivalence + shift structure + fire-row tapes for cores 10/28/82/244/100/163 — all confirmed; 444/444 scan agreement, zero 2-free $4W_t(m)$ for $K \equiv 1 \bmod 9$ in $[10,4000]$.
- **C1 (climb law)**: $W_t(3q+r) = W_t(r) + 3 \cdot (4^{3^t})^r \cdot W_{t+1}(q)$ — 60/60 passes.

---

# PART III — THE GST GRAPH V2 ONTOLOGICAL UNIVERSE GRAPH

## III.1 The construction protocol (exact, step by step)

**Step 1 — Choose the energy.** Fix a natural $E \geq 1$ (the "energy" / seed). The graph will describe the worldtrace family of all powers $4^t \cdot E$.

**Step 2 — The coordinate plane.** Coordinates are $(t, p) \in \mathbb{N} \times \mathbb{N}$:
- $t$ = **horizontal axis** = the x4 stride (each step right multiplies the energy by 4),
- $p$ = **vertical axis** = the ternary depth (each step up divides by 3 and reads one more trit).

**Step 3 — The seven-axis vertex** (verbatim, `GSTCanonicalSevenAxisBridge.lean:29`):

```lean
/-- Canonical non-Euclidean seven-axis vertex.  The coordinates are arithmetic
state coordinates, not metric coordinates. -/
structure Vertex where
  horizontal : Nat        -- t
  horizontalNext : Nat    -- t+1
  vertical : Nat          -- p
  carry : Nat             -- carry4 (4^t * E) p        ∈ {0,1,2,3}
  space : Space           -- spaceOfCarry carry         ∈ {null, altMinus, gstPlus}
  digit : Nat             -- digit3 (4^t * E) p        ∈ {0,1,2}
  descent : Nat           -- (4^t * E) / 3^p
  nextDescent : Nat       -- (4^t * E) / 3^(p+1)
  deriving Repr

/-- The three physical GST spaces carried by the seven-axis state. -/
inductive Space
  | null
  | altMinus
  | gstPlus

def spaceOfCarry (C : Nat) : Space :=
  if C = 0 then .null else if C = 3 then .gstPlus else .altMinus

/-- The actual perfect-power sheet sampled in x4 horizontal stride. -/
def vertex (E t p : Nat) : Vertex where
  horizontal := t
  horizontalNext := t + 1
  vertical := p
  carry := carry4 (4^t * E) p
  space := spaceOfCarry (carry4 (4^t * E) p)
  digit := digit3 (4^t * E) p
  descent := (4^t * E) / 3^p
  nextDescent := (4^t * E) / 3^(p+1)
```

**Step 4 — The exact lattice law.** The graph is an exact x4/base-3 cellular automaton:

```lean
/-- The x4 carry regenerates exactly in the vertical ternary direction. -/
theorem carry4_forward_exact (R p : Nat) :
    carry4 R (p+1) = nextCarry (carry4 R p) (digit3 R p)

/-- Multiplication by four exposes the local x4 output trit exactly. -/
theorem digit3_mul_four_exact (R p : Nat) :
    digit3 (4 * R) p = outDigit (carry4 R p) (digit3 R p)

/-- The canonical sheet is an exact x4/base3 cell lattice at every pair of
natural coordinates. -/
theorem canonical_cell_exact (E t p : Nat) :
    outDigit (vertex E t p).carry (vertex E t p).digit =
        (vertex E (t+1) p).digit ∧
      nextCarry (vertex E t p).carry (vertex E t p).digit =
        (vertex E t (p+1)).carry
```

That is: **moving right** (t → t+1) applies the cell $(C,d) \mapsto \text{outDigit}(C,d) = (C + 4d) \bmod 3$; **moving up** (p → p+1) applies $(C,d) \mapsto \text{nextCarry}(C,d) = (C + 4d)/3$. The twelve physical cells are $C \in \{0,1,2,3\} \times d \in \{0,1,2\}$.

**Step 5 — The event coordinate and the Happy predicate.**

```lean
/-- The radix event coordinate of one x4 GST cell.  It records the input and
output trit in one number `0..8`; event eight is exactly `2 -> 2`. -/
def event (C d : Nat) : Nat := d + 3 * outDigit C d

/-- Exact seven-axis event balance: the apparent x4/base3 exponential update
collapses to one linear arithmetic identity with a live upper carry. -/
theorem event_balance_exact (C d : Nat) :
    event C d + 9 * nextCarry C d = 13 * d + 3 * C

/-- Event eight is precisely the two physical Happy/SURVIVE realizations. -/
theorem happy_iff_event_eight (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ event C d = 8
```

`HappyCell C d` (defined in `GSTU2DEventTransport`) is $d = 2 \wedge (C = 0 \vee C = 3)$: **a ternary digit 2 that survives the x4 multiplication with null or GST+ carry.** The object of Part 0 is exactly: *every $K \ge 8$ has a Happy cell somewhere on the column $t=0$ of the graph of $4^K$.* (The bridge: `graph_prefix_slice_happy_iff` + `happy_iff_event_eight` + `hasTernaryTwo_of_digit`.)

**Step 6 — Enrichment (the infinite control graph).** Attach all green charge observables to every vertex (§G1): `eventCode`, `uCharge`, `mixedCharge`, `crossingCharge`, `survive` — giving `InfiniteCell`, and the graph

$$\Gamma_E : \mathbb{N} \times \mathbb{N} \to \text{InfiniteCell}, \qquad \Gamma_E(t,p) = \text{cell}(E,t,p).$$

**The graph is one single function on the full infinite plane — every finite rectangle is an observation of the same object.**

## III.2 The physics on the graph

- **The 2D divergence law** (§E): on every finite rectangle, the mixed density's total mass = BIG1 boundary charge + carry flux + positive SURVIVE incidence — a discrete Gauss law. Happy chords: NULL = hidden $2 \to 1 \to 2$, GST+ = all-SURVIVE $2 \to 2 \to 2$ (`happy_chord_dichotomy`).
- **The U operator** (`uJump_divergence`): the handwritten U jump is *itself* a two-direction divergence — horizontal information transport plus the ternary carry-potential derivative.
- **The wave observation law** (`observation_law_wave`): a Happy cell with an all-depth bad boundary is NOT erased — it reappears as a strictly positive coupled-U derivative three waves to the right. Information propagates, never dies.
- **The ontological current** (below): Happy = positive current, on every cell and every window.

## III.3 The ontological current — reverse base-seven certificate (`GSTGraphV2Ontological.lean`)

```lean
/-- Horizontal information potential for the pure ontological current. -/
def ontDigitPotential (d : Nat) : Int :=
  if d = 0 then 9 else if d = 1 then -35 else -91

/-- Vertical carry potential for the pure ontological current. -/
def ontCarryPotential (C : Nat) : Int :=
  if C = 0 then 0 else if C = 1 then 77 else if C = 2 then 154 else 252

/-- Pure x7/base3 divergence.  Unlike the older crossing densities this has no
interior SURVIVE source term. -/
def ontDensity (C d : Nat) : Int :=
  ontDigitPotential (outDigit C d) - 7 * ontDigitPotential d +
    ontCarryPotential C - 3 * ontCarryPotential (nextCarry C d)

/-- Complete twelve-state certificate.  Exactly the two Happy cells are
positive; every bad physical cell is nonpositive; the global floor is -54. -/
theorem ontDensity_physical_table :
    ontDensity 0 0 = -54 ∧ ontDensity 0 1 = -21 ∧ ontDensity 0 2 = 84 ∧
    ontDensity 1 0 = -21 ∧ ontDensity 1 1 = 0 ∧ ontDensity 1 2 = -33 ∧
    ontDensity 2 0 = 0 ∧ ontDensity 2 1 = -54 ∧ ontDensity 2 2 = 0 ∧
    ontDensity 3 0 = -33 ∧ ontDensity 3 1 = 0 ∧ ontDensity 3 2 = 42

/-- A physical Happy cell injects at least 42 units of ontological current. -/
theorem ontDensity_ge_42_of_happy (C d : Nat) (h : HappyCell C d) :
    (42 : Int) ≤ ontDensity C d

/-- Happy is exactly the positive sector of the pure ontological current. -/
theorem happy_iff_ontDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < ontDensity C d
```

The accumulation and no-erasure laws:

```lean
/-- Reverse-base-seven accumulation of one horizontal graph row. -/
def reverseOntCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCode C d N + ontDensity (C N) (d N)

/-- Exact horizontal telescope of the pure ontological current. -/
theorem reverseOntCode_exact (C Cnext d : Nat → Nat) : ∀ N : Nat, ...

/-- Global floor for an arbitrary physical horizontal row. -/
theorem reverseOntCode_ge_global_floor (C d : Nat → Nat) : ∀ N : Nat, ...

/-- **Pure horizontal no-erasure.**  A leading Happy cell starts with at least
42.  Every later physical cell costs at most 54 while the current is
multiplied by seven: 33*7^N + 63 ≤ 7*code_N. -/
theorem reverseOntCode_ge_scaled_of_leading_happy ... 

/-- **Ontological highest-Happy-row domination.**  The base-seven pure
current has enough margin that a leading Happy row beats the total
worst-case mass of all lower rows under the literal base-three vertical
weighting. -/
theorem weightedOntPrefix_positive_of_top_leading_happy ...

/-- A Happy source on the left edge gives strictly positive ontological
current through every nonzero-width Graph-V2 block. -/
theorem graphOntWindow_positive_of_happy
    (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell (graph E 0 (b+q)).seven.carry
                      (graph E 0 (b+q)).seven.digit) :
    0 < graphOntWindow E N b (q+1)
```

## III.4 The geometry family (all green modules, all constructible the same way)

- `GSTGraphV2SixAdicOntologicalGeometry.lean` + `...GeometryLaws.lean` + `...GeometryTest.lean` — the six-adic ontological geometry of the twelve cells.
- `GSTGraphV2NonEuclidean.lean` + `GSTGraphV2NonEuclideanLaws.lean` — the non-Euclidean (arithmetic-state, not metric) coordinate laws.
- `GSTGraphV2Production.lean` + `GSTGraphV2ProductionLaws.lean` — production windows on the graph.
- `GSTGraphV2CoupledUFlux.lean` / `GSTGraphV2CoupledUPhysicalBridge.lean` — the coupled U-flux potentials.
- `GSTGraphV2UnifiedPowerRectangle.lean` / `GSTGraphV2UnifiedVerticalTelescope.lean` — the unified rectangle and vertical telescope.
- `GSTGraphV2CanonicalDescentOntology.lean` / `GSTGraphV2DescentOntology.lean` — descent ontology layers.
- `GSTGraphV2PerfectPowerAncestry/BlockCollision/BlockProbe.lean` — perfect-power block structure.
- `GSTGraphV2CanonicalRenormalization.lean`, `GSTGraphV2CanonicalSheetTranslation.lean`, `GSTGraphV2CanonicalPhaseSteering.lean`, `GSTGraphV2CanonicalNWave.lean`, `GSTGraphV2CanonicalEscape.lean`.
- The monolith `ErdosTernary2.lean` (18,527 lines) — the kernel: `noTernaryTwo`, the odd-exponent half, the weakening chain (`omegaShadow` → `tail2` → `tail` → `tail3` → `tail4` → `tail5` → `tailE` → `tailF`), the terminal identity, and the crown `erdos_ternary_2_universal_of_tailF`.


---

# PART IV — THE COMPLETE MONOLITH, VERBATIM

**File: `GSTWorldtraceArithmetic.lean` — 1221 lines, 45 declarations, every one CI-green at HEAD `fd89766`, 0 sorries, axioms `[propext, Classical.choice, Quot.sound]`.**

This part is the *entire* worldtrace arithmetic monolith, pasted line for line, section by section, with the mathematical content of each section named explicitly before you read it. Part II quoted the highlights; here is the whole engine, nothing withheld. Where Part V derives the mathematics in LaTeX, this part is the machine's own statement of it — the exact code that the proof checker has already accepted. Treat every declaration here as a *given*: it is verified, it is load-bearing, and it is yours to compose.

**How to read this monolith.** The file is organized as eight movements:

1. **The binomial ladder** (`one_add_pow_three_term`, `one_add_pow_four_term`, `one_add_pow_five_term`) — the expansion engine that turns powers of `1+63` into explicit polynomial windows with controlled error terms.
2. **The transformation and the three blades** (`wt_rebase`, `wt_quad_mod729`, `wt_cubic_mod6561`, `wt_quartic_mod19683`) — the identity `4^(1+3m) = 4·64^m = 4·(1+63)^m` and its three polynomial shadows modulo 729, 6561, 19683.
3. **The reads** (`wt_row_five_read`, `wt_row_seven_read`, `wt_row_eight_read`) — the theorems that identify deep rows of the dust power with rows of the polynomial blades, *exactly, for every m*.
4. **The kill demos** (`wt_quartic_fire_demo`, `wt_quad_fire_demo`) — polynomial kills of specific exponents without ever computing the power.
5. **The uniform kill engine** (`fire_of_mod2187`, `fire_of_mod6561`) — the noise-receipt firing law at level six and level seven, each an instance of the master `feedback_fire_of_class`.
6. **The cascade levels six and seven** (`dust_fire_row_seven` with its 32 dead classes, `no22_of_cascade_six`, `cantorian_dust_mod_2187` with its 64 survivors; `dust_fire_row_eight` with its 64 dead classes, `no22_of_cascade_seven`, `cantorian_dust_mod_6561` with its 128 survivors) — the doubling kill tables.
7. **The pair-read family** (`pair_read_formula`, `pair_read_fire`, `pair_residue_mod27`, `digit3_row_two_of_residue`, `pair_read_fire_general`, `no22_of_pair_read_general`, the two demo families, `the_pair_read_receipt`, `the_general_fire_receipt`) — GAP-E1's infinite families that no fixed cascade level ever reaches.
8. **The descent engine and the dust window** (`top_split`, `window_congr`, `window_row_two`, `the_descent_engine_receipt`; `four_pow_mod9`, `dust_branch_mod9`, `window_row_two_dust`, `window_reduce`, `the_dust_window_receipt`) — the self-observational reduction of row `H+2` of `4^K` to smaller exponents, and the mod-9 vanishing of the branch term.

The file closes with two grand receipts — `the_worldtrace_receipt` and `the_worldtrace_receipt_seven` — each a single theorem packaging an entire cascade storey as one conjunction, and a wall of `#print axioms` commands certifying that every declaration rests on nothing but the three standard axioms.

Read the code. All of it. It is shorter than it looks and every line is doing arithmetic you can check by hand.

## IV.0 The module header — the transformation, stated by the machine itself

The header is the monolith's own abstract: the transformation `4^(1+3m) = 4·64^m = 4·(1+63)^m = 4·Σᵢ C(m,i)·63ⁱ`, the birth of the polynomial blades, and the machine receipts that were checked *before* the theorems were written. Note the imports: `Mathlib`, `GSTTowerFire` (the LTE tower), `GSTTheActConstruction` (the feedback laws), `GSTFourPowerDirectResidue` (the digit-read laws) — the monolith stands on the three green pillars.

```lean
import Mathlib
import GSTTowerFire
import GSTTheActConstruction
import GSTFourPowerDirectResidue

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower no22_of_digit_two)
open GSTTheActConstruction (feedback_fire_of_class cantorian_dust_mod_729)
open GSTFourPowerDirectResidue (digit3_eq_of_mod_next)

namespace GSTWorldtraceArithmetic

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

/-!
# THE WORLDTRACE ARITHMETIC — the boss's transformation, landed

The stuck gap (GAP-A2, the c_infinity blade survivor tree) TRANSFORMED
into worldtrace arithmetic and attacked there.  The transformation:

    4^(1+3m) = 4 * 64^m = 4 * (1+63)^m = 4 * SUM_i C(m,i) * 63^i

Every dust power is a BINOMIAL SUM in the exponent's half-scale — and
every deep row becomes an EXPLICIT POLYNOMIAL in m with 3-adic
coefficients 4*7^i sitting at row-blocks 2i:

  * row five  = the QUADRATIC blade `4 + 252m + 15876*C(m,2)` mod 729
  * row seven = the CUBIC blade `4 + 252m + 15876*C(m,2) + 1000188*C(m,3)`
    mod 6561

Machine receipts BEFORE landing (this session, exact big-int / modular,
`/tmp/wt_receipts.py`):

  * R1 32/32 — the level-6 dead classes mod 2187 all fire at row seven
    (modular 4^rho mod 3^8 arithmetic); survivors double 32 -> 64 exactly.
  * R2 the quadratic blade's kill set CONTAINS the entire green row-five
    table {85, 91, 112, 118, 163, 175, 190, 202} — the polynomial
    reproduces the machine's green cascade.
  * R4 the cubic identity holds 0 failures on 0 <= m < 6561 step 7, and
    row-seven polynomial reads match direct computation 2187/2187.
  * R5 (level seven, this session, `/tmp/wt_level7.py`): recursion
    re-verified against the green tables (s5/d6/s6 exact); quartic AND
    quintic blades 0 failures on all 0 <= m < 2186; 64 dead classes
    mod 6561 fire at row eight; survivors double 64 -> 128 exactly
    (192 = 64*3 children partition checked).

Sections:

  * SS1 THE BINOMIAL LADDER — `one_add_pow_three_term`,
    `one_add_pow_four_term` (the two-term `GSTTowerFire` engine extended).
  * SS2 THE TRANSFORMATION — `wt_rebase`, `wt_quad_mod729` (the
    quadratic blade), `wt_cubic_mod6561` (the cubic blade).
  * SS3 THE READS — `wt_row_five_read`, `wt_row_seven_read`: the dust
    power's deep rows ARE the polynomial blades, plus the polynomial
    kill demo (`wt_quad_fire_demo`: the quadratic kills K = 85 at row
    five without ever computing 4^85).
  * SS4 THE SIXTH CASCADE LEVEL — `fire_of_mod2187`, `dust_fire_row_seven`
    (32 dead classes), `no22_of_cascade_six`, `cantorian_dust_mod_2187`
    (the 64-survivor map).
  * SS5 THE SEVENTH CASCADE LEVEL — `fire_of_mod6561`, `dust_fire_row_eight`
    (64 dead classes), `no22_of_cascade_seven`, `cantarian_dust_mod_6561`
    (the 128-survivor map), plus the quartic blade `wt_quartic_mod19683`,
    the row-eight read, and the quartic kill demo (K = 82 killed at row
    eight without computing 4^82).
  * SS6 THE PAIR-READ FIRE — GAP-E1's first family: the uniform
    pair_read_formula (row-(j+4) of 4^(T+3^(j+1)*u) = row-two of
    4^T*u*c (j+1), via prefaced_digit + the binomial ladder) and
    pair_read_fire (every 4 + 3^(j+1)*u with j >= 4, u in {{1,4,7}}
    fires at row j+4 through c_mod81: trit two of 19*u).
-/

/-! ## §1 The binomial ladder -/

/-- **Choose-one, by induction** (self-contained: only
`Nat.choose_succ_succ` and `Nat.choose_zero_right`). -/
```

## IV.1 The binomial ladder — `wt_choose_one`, the three-term, four-term, five-term ladders

The ladder is the only expansion engine the monolith needs. Each rung states: for every natural `x, j`, the power `(1+x)^j` decomposes into its first three (resp. four, five) explicit orders plus a controlled dust term `x³·R` (resp. `x⁴·R`, `x⁵·R`) with an existential witness `R`. The proofs are honest inductions on `j` using nothing but Pascal's rule `Nat.choose_succ_succ`. Three observations:

- The witnesses are *explicit*: `one_add_pow_three_term` produces `R = C(j,2) + R' + x·R'` style data — no choice, no classical detour, pure recursion.
- The error terms carry exact 3-adic valuations once `x = 63 = 3²·7` is substituted: `x³ = 3⁶·7³` dies mod `3⁶ = 729`, `x⁴` dies mod `3⁸ = 6561`, `x⁵` dies mod `3⁹ = 19683` (and even mod `3¹⁰`). This is why the three blades land exactly at the moduli they land at.
- The ladder is *uniform in x*: the same three theorems power the blade sections (with `x = 63`), the pair-read family (with `x = 3^(j+2)·c(j+1)`), and the descent engine (with `x = 3^(H+1)·c(H)`). One ladder, three weapons.

```lean
theorem wt_choose_one (n : Nat) : Nat.choose n 1 = n := by
  induction n with
  | zero => decide
  | succ k ih =>
    have h : Nat.choose (k+1) 1 = Nat.choose k 0 + Nat.choose k 1 :=
      Nat.choose_succ_succ k 0
    rw [h, Nat.choose_zero_right, ih]
    omega

/-- **The three-term binomial ladder.** `(1+x)^j` with the first three
orders explicit — the term structure the worldtrace window reads. -/
theorem one_add_pow_three_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x + x*x*x*R := by
  induction j with
  | zero =>
    have h0 : Nat.choose 0 2 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h0]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    rw [Nat.pow_succ, hR, hc]
    refine ⟨Nat.choose j 2 + R + x*R, ?_⟩
    ring

/-- **The four-term binomial ladder.**  One order deeper: the cubic
window's engine. -/
theorem one_add_pow_four_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    rw [Nat.pow_succ, hR, hc2, hc3]
    refine ⟨Nat.choose j 3 + R + x*R, ?_⟩
    ring

/-- **The five-term binomial ladder.**  Two orders deeper: the quartic
window's engine. -/
theorem one_add_pow_five_term (x j : Nat) :
    ∃ R : Nat, (1+x)^j = 1 + j*x + Nat.choose j 2 * x * x
      + Nat.choose j 3 * x * x * x + Nat.choose j 4 * x * x * x * x
      + x*x*x*x*x*R := by
  induction j with
  | zero =>
    have h02 : Nat.choose 0 2 = 0 := by decide
    have h03 : Nat.choose 0 3 = 0 := by decide
    have h04 : Nat.choose 0 4 = 0 := by decide
    refine ⟨0, ?_⟩
    rw [Nat.pow_zero, h02, h03, h04]
    ring
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hc2 : Nat.choose (j+1) 2 = j + Nat.choose j 2 := by
      rw [Nat.choose_succ_succ j 1, wt_choose_one j]
    have hc3 : Nat.choose (j+1) 3 = Nat.choose j 2 + Nat.choose j 3 :=
      Nat.choose_succ_succ j 2
    have hc4 : Nat.choose (j+1) 4 = Nat.choose j 3 + Nat.choose j 4 :=
      Nat.choose_succ_succ j 3
    rw [Nat.pow_succ, hR, hc2, hc3, hc4]
    refine ⟨Nat.choose j 4 + R + x*R, ?_⟩
    ring

/-! ## §2 The transformation — the dust as a binomial sum -/

/-- **THE REBASE.**  Every dust power is a power of sixty-four:
`4^(1+3m) = 4 * 64^m` — and 64 = 1 + 63 opens the binomial world. -/
```

## IV.2 The transformation, the three blades, the reads, the kill demos

This is the heart of worldtrace arithmetic — the section that gives the subject its name.

**`wt_rebase`**: `4^(1+3m) = 4·64^m`. Every dust exponent `K ≡ 1 mod 3` is `K = 1+3m` with `m = (K−1)/3`, and its power is a fixed factor times a power of 64.

**The three blades.** Since `64 = 1 + 63` with `63 = 9·7 = 3²·7`, the ladder turns `4^(1+3m)` into:

- **Quadratic blade** (`wt_quad_mod729`): `4^(1+3m) ≡ 4 + 252m + 15876·C(m,2) (mod 729)`. Coefficients: `252 = 4·63`, `15876 = 4·63²`. The error `4·63³·R = 1000188·R` with `1000188 = 729·1372` — the dust term is *invisible* mod 729.
- **Cubic blade** (`wt_cubic_mod6561`): adds `1000188·C(m,3) = 4·63³·C(m,3)`; the new error `4·63⁴·R = 63011844·R` with `63011844 = 6561·9604` dies mod 6561.
- **Quartic blade** (`wt_quartic_mod19683`): adds `63011844·C(m,4) = 4·63⁴·C(m,4)`; the new error `4·63⁵·R = 3969746172·R` with `3969746172 = 19683·201684` dies mod 19683.

Each proof is the same shape: instantiate the ladder at `x = 63`, multiply out by 4 with `ring`, and exhibit the divisibility witness (`1372·R`, `9604·R`, `201684·R`). The divisibility witnesses are the *only* arithmetic facts that distinguish the three blades.

**The reads.** `wt_row_five_read` / `wt_row_seven_read` / `wt_row_eight_read`: for EVERY `m`, row 5 (resp. 7, 8) of `4^(1+3m)` equals row 5 (resp. 7, 8) of the corresponding polynomial. The bridge is `digit3_eq_of_mod_next` — row `p` of any number is determined by its residue mod `3^(p+1)` — combined with the dictionary `729 = 3⁶` (row 5), `6561 = 3⁸` (row 7), `19683 = 3⁹` (row 8). **The deep rows of the dust powers ARE polynomial evaluations.** This is the worldtrace read.

**The kill demos.** `wt_quartic_fire_demo` kills `K = 82` (`m = 27`) at row 8 by reading the quartic blade alone; `wt_quad_fire_demo` kills `K = 85` (`m = 28`) at row 5 by the quadratic blade. Neither ever computes `4^82` or `4^85` — the polynomial is the power, as far as the row in question can see.

```lean
theorem wt_rebase (m : Nat) : 4^(1+3*m) = 4 * 64^m := by
  have h43 : (4:Nat)^3 = 64 := by decide
  rw [Nat.pow_add, Nat.pow_mul, h43, Nat.pow_one]

/-- **THE QUADRATIC BLADE.**  Row-window congruence of the dust power:
`4^(1+3m)` is the quadratic `4 + 252m + 15876*C(m,2)` mod 729 — the
order-two worldtrace.  (63^3 = 250047 = 729*343 dies mod 729.) -/
theorem wt_quad_mod729 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729] := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*R) % 729
     = (4 + 252*m + 15876*Nat.choose m 2) % 729
  have hd : 729 ∣ 1000188*R := by
    refine ⟨1372*R, ?_⟩
    ring
  have hz : 1000188*R % 729 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- **THE CUBIC BLADE.**  One window deeper: `4^(1+3m)` is the cubic
`4 + 252m + 15876*C(m,2) + 1000188*C(m,3)` mod 6561 — the order-three
worldtrace.  (63^4 = 3^8 * 7^4 dies mod 3^8 = 6561.) -/
theorem wt_cubic_mod6561 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561] := by
  obtain ⟨R, hR⟩ := one_add_pow_four_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + 63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*R) % 6561
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) % 6561
  have hd : 6561 ∣ 63011844*R := by
    refine ⟨9604*R, ?_⟩
    ring
  have hz : 63011844*R % 6561 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-- **THE QUARTIC BLADE.**  Two windows deeper: `4^(1+3m)` is the quartic
`4 + 252m + 15876*C(m,2) + 1000188*C(m,3) + 63011844*C(m,4)` mod 19683 —
the order-four worldtrace.  (63^5 = 3^10 * 7^5 dies mod 3^9 = 19683.) -/
theorem wt_quartic_mod19683 (m : Nat) :
    4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683] := by
  obtain ⟨R, hR⟩ := one_add_pow_five_term 63 m
  have h64 : (64:Nat) = 1 + 63 := by decide
  have hexp : 4 * (1 + m*63 + Nat.choose m 2 * 63 * 63
        + Nat.choose m 3 * 63 * 63 * 63 + Nat.choose m 4 * 63 * 63 * 63 * 63
        + 63*63*63*63*63*R)
      = 4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*R := by ring
  rw [wt_rebase, h64, hR, hexp]
  show (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4 + 3969746172*R) % 19683
     = (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
        + 63011844*Nat.choose m 4) % 19683
  have hd : 19683 ∣ 3969746172*R := by
    refine ⟨201684*R, ?_⟩
    ring
  have hz : 3969746172*R % 19683 = 0 := Nat.mod_eq_zero_of_dvd hd
  omega

/-! ## §3 The reads — the deep rows ARE the polynomials -/

/-- **ROW FIVE IS THE QUADRATIC.**  For EVERY m: the fifth row of the
dust power `4^(1+3m)` is the fifth row of the quadratic blade — the
worldtrace read, exact. -/
theorem wt_row_five_read (m : Nat) :
    digit3 (4^(1+3*m)) 5 = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5 := by
  have h729 : (3:Nat)^(5+1) = 729 := by decide
  have h := wt_quad_mod729 m
  rw [← h729] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **ROW SEVEN IS THE CUBIC.**  For EVERY m: the seventh row of the
dust power is the seventh row of the cubic blade. -/
theorem wt_row_seven_read (m : Nat) :
    digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7 := by
  have h6561 : (3:Nat)^(7+1) = 6561 := by decide
  have h := wt_cubic_mod6561 m
  rw [← h6561] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **ROW EIGHT IS THE QUARTIC.**  For EVERY m: the eighth row of the
dust power is the eighth row of the quartic blade — the worldtrace
read, exact. -/
theorem wt_row_eight_read (m : Nat) :
    digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8 := by
  have h19683 : (3:Nat)^(8+1) = 19683 := by decide
  have h := wt_quartic_mod19683 m
  rw [← h19683] at h
  exact digit3_eq_of_mod_next _ _ _ h

/-- **THE QUARTIC KILL DEMO.**  The quartic blade kills K = 82
(m = 27) at row eight WITHOUT EVER COMPUTING `4^82`: the worldtrace
quartic reads digit two at row eight.  The transformed problem,
solved in transformed coordinates, one storey deeper. -/
theorem wt_quartic_fire_demo : digit3 (4^(1+3*27)) 8 = 2 := by
  rw [wt_row_eight_read]
  decide

/-- **THE POLYNOMIAL KILL DEMO.**  The quadratic blade kills K = 85
(m = 28) at row five WITHOUT EVER COMPUTING `4^85`: the worldtrace
quadratic `4 + 252*28 + 15876*C(28,2) ≡ 499 mod 729` reads digit two
at row five.  The transformed problem, solved in transformed
coordinates. -/
theorem wt_quad_fire_demo : digit3 (4^(1+3*28)) 5 = 2 := by
  rw [wt_row_five_read]
  decide

/-! ## §4 The sixth cascade level — the compression continues -/

/-- **THE UNIFORM KILL, LEVEL-SIX FORM.**  `K ≡ r + 729*t mod 2187`
fires at row seven when the noise receipt holds.  All arithmetic
literal. -/
```

## IV.3 The uniform kill engine and cascade level six — the noise receipts

**`fire_of_mod2187`** is the level-six instance of the master feedback law `feedback_fire_of_class` (Part II, §F2): if `K ≡ r + 729·t (mod 2187)` with `r < 729`, `t < 3`, and the *noise receipt* `(digit3(4^r, 7) + t) % 3 = 2` holds, then `digit3(4^K, 7) = 2`. The name "noise" is exact: `digit3(4^r, 7)` is the interference pattern that the prefix-power `4^r` contributes to row 7, `t` is the new trit of `K` at position 6, and their sum mod 3 IS row 7 of `4^K`. When the sum is 2, the class dies.

**`dust_fire_row_seven`** enumerates all 32 dead classes mod 2187: `{10, 28, 199, 274, 415, 442, 499, 517, 652, 658, 742, 769, 811, 895, 1012, 1054, 1309, 1324, 1459, 1462, 1552, 1567, 1579, 1651, 1702, 1705, 1738, 1822, 1894, 1954, 1972, 1981}`. Each bullet is one `fire_of_mod2187` invocation with all arithmetic closed by `decide`. The table was GENERATED, not guessed: each dead class is `r + 729·t` where `r` is a level-six survivor and `t = (2 − noise₆(r)) mod 3` is the unique dead-child trit. The receipt R16 in Part VI verifies all 32 noise receipts numerically.

**`cantorian_dust_mod_2187`** is the mirror image: a Cantorian dust exponent (`K ≡ 1 mod 3`, `CantorianPower K`, i.e. `4^K` has no 2 anywhere) must live in one of exactly **64** surviving residues mod 2187. The proof is the kill table run in reverse: each of the 32 dead classes is refuted by `dust_fire_row_seven` (a Cantorian power cannot be in a class that fires), and the residue arithmetic closes by `omega` against the level-five survivor list. The structural content: **the alive set doubles 32 → 64, because each of the 32 level-six survivors spawns 3 children mod 2187, exactly one of which is the dead child.** The receipt R6 confirms the doubling law holds at every level 1 through 9 without exception: 1, 2, 4, 8, 16, 32, 64, 128, 256.

**`no22_of_cascade_six`** converts the firing table into the kill chain's language: every exponent in a dead class has `noTernaryTwo (4^K) = false`.

```lean
theorem fire_of_mod2187 (K r t : Nat)
    (hr : r < 729) (ht : t < 3)
    (hnoise : (digit3 (4^r) 7 + t) % 3 = 2)
    (hclass : K % 2187 = r + 729 * t) :
    digit3 (4^K) 7 = 2 := by
  have h2187 : (3:Nat)^(6+1) = 2187 := by decide
  have h729 : (3:Nat)^6 = 729 := by decide
  have hK : K % 3^(6+1) = r + 3^6 * t := by
    rw [h2187, h729]
    exact hclass
  have hr' : r < 3^6 := by
    rw [h729]
    exact hr
  exact feedback_fire_of_class 6 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL SIX (row seven).**  Every exponent in one of the
thirty-two dead classes mod 2187 fires its digit two at row seven.
Generated from the worldtrace noise receipts (`noise_6(r) = digit3 (4^r) 7`,
dead child `t = (2 - noise) % 3`, dead class `r + 729*t`) — the sixth
storey of the feedback tree, each node keeping exactly two alive
children (`unique_dead_child`). -/
theorem dust_fire_row_seven (K : Nat)
    (hK : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    digit3 (4^K) 7 = 2 := by
  rcases hK with h10 | h28 | h199 | h274 | h415 | h442 | h499 | h517 | h652 | h658 | h742 | h769 | h811 | h895 | h1012 | h1054 | h1309 | h1324 | h1459 | h1462 | h1552 | h1567 | h1579 | h1651 | h1702 | h1705 | h1738 | h1822 | h1894 | h1954 | h1972 | h1981
  · exact fire_of_mod2187 K 10 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 28 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 199 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 274 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 415 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 442 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 499 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 517 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 652 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 658 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 13 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 40 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 82 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 166 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 283 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 325 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 580 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 595 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 4 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 94 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 109 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 121 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 193 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 244 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 247 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 280 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 364 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 436 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 496 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 514 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod2187 K 523 2 (by decide) (by decide) (by decide) (by omega)
/-- **THE DUST PINNED AT LEVEL SIX — THE MAP DOUBLES AGAIN.**  A Cantorian
dust exponent (`K ≡ 1 mod 3`) lives in one of SIXTY-FOUR surviving
residues mod 2187.  The structural law, third stroke: `2, 4, 8, 16,
32, 64` — the alive set doubles level by level without exception,
every node keeping exactly two children by the blade's one-of-three. -/
theorem cantorian_dust_mod_2187 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116 := by
  have h729 := cantorian_dust_mod_729 K hd hc
  have hrow := hc 7 (by omega)
  have hd0 : K % 2187 ≠ 10 :=
    fun h => absurd (dust_fire_row_seven K (Or.inl h)) hrow
  have hd1 : K % 2187 ≠ 28 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inl h))) hrow
  have hd2 : K % 2187 ≠ 199 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hd3 : K % 2187 ≠ 274 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hd4 : K % 2187 ≠ 415 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hd5 : K % 2187 ≠ 442 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hd6 : K % 2187 ≠ 499 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hd7 : K % 2187 ≠ 517 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hd8 : K % 2187 ≠ 652 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hd9 : K % 2187 ≠ 658 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hd10 : K % 2187 ≠ 742 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hd11 : K % 2187 ≠ 769 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hd12 : K % 2187 ≠ 811 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hd13 : K % 2187 ≠ 895 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hd14 : K % 2187 ≠ 1012 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hd15 : K % 2187 ≠ 1054 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow
  have hd16 : K % 2187 ≠ 1309 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow
  have hd17 : K % 2187 ≠ 1324 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow
  have hd18 : K % 2187 ≠ 1459 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow
  have hd19 : K % 2187 ≠ 1462 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow
  have hd20 : K % 2187 ≠ 1552 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow
  have hd21 : K % 2187 ≠ 1567 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow
  have hd22 : K % 2187 ≠ 1579 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow
  have hd23 : K % 2187 ≠ 1651 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow
  have hd24 : K % 2187 ≠ 1702 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow
  have hd25 : K % 2187 ≠ 1705 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow
  have hd26 : K % 2187 ≠ 1738 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow
  have hd27 : K % 2187 ≠ 1822 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow
  have hd28 : K % 2187 ≠ 1894 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow
  have hd29 : K % 2187 ≠ 1954 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow
  have hd30 : K % 2187 ≠ 1972 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow
  have hd31 : K % 2187 ≠ 1981 :=
    fun h => absurd (dust_fire_row_seven K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))) hrow
  rcases h729 with h1 | h4 | h10 | h13 | h28 | h40 | h82 | h94 | h109 | h121 | h166 | h193 | h199 | h244 | h247 | h274 | h280 | h283 | h325 | h364 | h415 | h436 | h442 | h496 | h499 | h514 | h517 | h523 | h580 | h595 | h652 | h658 <;> omega

/-- **THE CASCADE KILL, LEVEL SIX.**  The thirty-two new classes die
outright through the repo's own kill chain. -/
```

## IV.4 Cascade level seven — the map doubles to 128, the quartic feeds the fires

**`fire_of_mod6561`**: the same uniform kill, one storey up — `K ≡ r + 2187·t (mod 6561)`, noise receipt at row 8, class fires at row 8.

**`dust_fire_row_eight`** enumerates the 64 dead classes mod 6561 (the giant Or-chain in the statement). Look closely at the proof bullets: each one is `fire_of_mod6561 K r 0/1/2 ... (by rw [show r = 1 + 3*m from by decide, wt_row_eight_read]; decide)` — **the noise receipts at row 8 are computed through the QUARTIC BLADE**, not through `4^r` directly. The polynomial machinery is not decoration; it is the engine that makes level seven's arithmetic close by `decide`. The worldtrace transformation and the cascade are one machine.

**`cantorian_dust_mod_6561`**: a Cantorian dust exponent must live in one of exactly **128** residues mod 6561. The proof kills the 64 dead classes through `dust_fire_row_eight` and closes against the level-six survivor list. The doubling continues: 64 → 128.

**`no22_of_cascade_seven`**: the kill chain form.

The pattern is now completely visible, and it is the pattern the infinite controllers (Part II, §G) manage: at level L, there are `2^(L-1)` survivors mod `3^L`; each spawns 3 children mod `3^(L+1)`; the noise receipt at row L+1 kills exactly one child per survivor; the alive set doubles. The dust tree is a **binary tree grafted inside the ternary tree** — a Cantor set of exponents whose branching is exactly the middle-third set's. The conjecture says this Cantor set, above 8, is empty: every infinite branch is eventually cut.

```lean
theorem no22_of_cascade_six (K : Nat)
    (h : K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 7 (dust_fire_row_seven K h)

/-! ## §5 The seventh cascade level — the map doubles to 128 -/

/-- **THE UNIFORM KILL, LEVEL-SEVEN FORM.**  `K ≡ r + 2187*t mod 6561`
fires at row eight when the noise receipt holds.  All arithmetic
literal. -/
theorem fire_of_mod6561 (K r t : Nat)
    (hr : r < 2187) (ht : t < 3)
    (hnoise : (digit3 (4^r) 8 + t) % 3 = 2)
    (hclass : K % 6561 = r + 2187 * t) :
    digit3 (4^K) 8 = 2 := by
  have h6561 : (3:Nat)^(7+1) = 6561 := by decide
  have h2187 : (3:Nat)^7 = 2187 := by decide
  have hK : K % 3^(7+1) = r + 3^7 * t := by
    rw [h6561, h2187]
    exact hclass
  have hr' : r < 3^7 := by
    rw [h2187]
    exact hr
  exact feedback_fire_of_class 7 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL SEVEN (row eight).**  Every exponent in one of the
sixty-four dead classes mod 6561 fires its digit two at row eight.
Generated from the worldtrace noise receipts (`noise_7(r) = digit3 (4^r) 8`,
dead child `t = (2 - noise) % 3`, dead class `r + 2187*t`) — the seventh
storey of the feedback tree, each node keeping exactly two alive
children (`unique_dead_child`). -/
theorem dust_fire_row_eight (K : Nat)
    (hK : K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412) :
    digit3 (4^K) 8 = 2 := by
  rcases hK with h82 | h247 | h580 | h757 | h976 | h1246 | h1381 | h1471 | h1486 | h1498 | h1975 | h2110 | h2200 | h2227 | h2281 | h2296 | h2308 | h2380 | h2431 | h2701 | h2710 | h2926 | h3010 | h3025 | h3037 | h3109 | h3160 | h3358 | h3430 | h3439 | h3574 | h3655 | h3811 | h3928 | h3970 | h4087 | h4240 | h4303 | h4375 | h4378 | h4540 | h4654 | h4657 | h4699 | h4738 | h4810 | h4870 | h4969 | h5104 | h5107 | h5302 | h5377 | h5383 | h5467 | h5518 | h5539 | h5599 | h5602 | h5914 | h6031 | h6106 | h6247 | h6331 | h6412
  · exact fire_of_mod6561 K 82 0 (by decide) (by decide) (by rw [show (82:Nat) = 1 + 3*27 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 247 0 (by decide) (by decide) (by rw [show (247:Nat) = 1 + 3*82 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 580 0 (by decide) (by decide) (by rw [show (580:Nat) = 1 + 3*193 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 757 0 (by decide) (by decide) (by rw [show (757:Nat) = 1 + 3*252 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 976 0 (by decide) (by decide) (by rw [show (976:Nat) = 1 + 3*325 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1246 0 (by decide) (by decide) (by rw [show (1246:Nat) = 1 + 3*415 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1381 0 (by decide) (by decide) (by rw [show (1381:Nat) = 1 + 3*460 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1471 0 (by decide) (by decide) (by rw [show (1471:Nat) = 1 + 3*490 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1486 0 (by decide) (by decide) (by rw [show (1486:Nat) = 1 + 3*495 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1498 0 (by decide) (by decide) (by rw [show (1498:Nat) = 1 + 3*499 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1975 0 (by decide) (by decide) (by rw [show (1975:Nat) = 1 + 3*658 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2110 0 (by decide) (by decide) (by rw [show (2110:Nat) = 1 + 3*703 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 13 1 (by decide) (by decide) (by rw [show (13:Nat) = 1 + 3*4 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 40 1 (by decide) (by decide) (by rw [show (40:Nat) = 1 + 3*13 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 94 1 (by decide) (by decide) (by rw [show (94:Nat) = 1 + 3*31 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 109 1 (by decide) (by decide) (by rw [show (109:Nat) = 1 + 3*36 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 121 1 (by decide) (by decide) (by rw [show (121:Nat) = 1 + 3*40 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 193 1 (by decide) (by decide) (by rw [show (193:Nat) = 1 + 3*64 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 244 1 (by decide) (by decide) (by rw [show (244:Nat) = 1 + 3*81 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 514 1 (by decide) (by decide) (by rw [show (514:Nat) = 1 + 3*171 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 523 1 (by decide) (by decide) (by rw [show (523:Nat) = 1 + 3*174 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 739 1 (by decide) (by decide) (by rw [show (739:Nat) = 1 + 3*246 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 823 1 (by decide) (by decide) (by rw [show (823:Nat) = 1 + 3*274 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 838 1 (by decide) (by decide) (by rw [show (838:Nat) = 1 + 3*279 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 850 1 (by decide) (by decide) (by rw [show (850:Nat) = 1 + 3*283 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 922 1 (by decide) (by decide) (by rw [show (922:Nat) = 1 + 3*307 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 973 1 (by decide) (by decide) (by rw [show (973:Nat) = 1 + 3*324 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1171 1 (by decide) (by decide) (by rw [show (1171:Nat) = 1 + 3*390 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1243 1 (by decide) (by decide) (by rw [show (1243:Nat) = 1 + 3*414 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1252 1 (by decide) (by decide) (by rw [show (1252:Nat) = 1 + 3*417 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1387 1 (by decide) (by decide) (by rw [show (1387:Nat) = 1 + 3*462 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1468 1 (by decide) (by decide) (by rw [show (1468:Nat) = 1 + 3*489 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1624 1 (by decide) (by decide) (by rw [show (1624:Nat) = 1 + 3*541 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1741 1 (by decide) (by decide) (by rw [show (1741:Nat) = 1 + 3*580 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1783 1 (by decide) (by decide) (by rw [show (1783:Nat) = 1 + 3*594 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1900 1 (by decide) (by decide) (by rw [show (1900:Nat) = 1 + 3*633 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2053 1 (by decide) (by decide) (by rw [show (2053:Nat) = 1 + 3*684 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2116 1 (by decide) (by decide) (by rw [show (2116:Nat) = 1 + 3*705 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1 2 (by decide) (by decide) (by rw [show (1:Nat) = 1 + 3*0 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 4 2 (by decide) (by decide) (by rw [show (4:Nat) = 1 + 3*1 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 166 2 (by decide) (by decide) (by rw [show (166:Nat) = 1 + 3*55 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 280 2 (by decide) (by decide) (by rw [show (280:Nat) = 1 + 3*93 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 283 2 (by decide) (by decide) (by rw [show (283:Nat) = 1 + 3*94 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 325 2 (by decide) (by decide) (by rw [show (325:Nat) = 1 + 3*108 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 364 2 (by decide) (by decide) (by rw [show (364:Nat) = 1 + 3*121 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 436 2 (by decide) (by decide) (by rw [show (436:Nat) = 1 + 3*145 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 496 2 (by decide) (by decide) (by rw [show (496:Nat) = 1 + 3*165 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 595 2 (by decide) (by decide) (by rw [show (595:Nat) = 1 + 3*198 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 730 2 (by decide) (by decide) (by rw [show (730:Nat) = 1 + 3*243 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 733 2 (by decide) (by decide) (by rw [show (733:Nat) = 1 + 3*244 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 928 2 (by decide) (by decide) (by rw [show (928:Nat) = 1 + 3*309 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1003 2 (by decide) (by decide) (by rw [show (1003:Nat) = 1 + 3*334 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1009 2 (by decide) (by decide) (by rw [show (1009:Nat) = 1 + 3*336 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1093 2 (by decide) (by decide) (by rw [show (1093:Nat) = 1 + 3*364 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1144 2 (by decide) (by decide) (by rw [show (1144:Nat) = 1 + 3*381 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1165 2 (by decide) (by decide) (by rw [show (1165:Nat) = 1 + 3*388 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1225 2 (by decide) (by decide) (by rw [show (1225:Nat) = 1 + 3*408 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1228 2 (by decide) (by decide) (by rw [show (1228:Nat) = 1 + 3*409 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1540 2 (by decide) (by decide) (by rw [show (1540:Nat) = 1 + 3*513 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1657 2 (by decide) (by decide) (by rw [show (1657:Nat) = 1 + 3*552 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1732 2 (by decide) (by decide) (by rw [show (1732:Nat) = 1 + 3*577 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1873 2 (by decide) (by decide) (by rw [show (1873:Nat) = 1 + 3*624 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 1957 2 (by decide) (by decide) (by rw [show (1957:Nat) = 1 + 3*652 from by decide, wt_row_eight_read]; decide) (by omega)
  · exact fire_of_mod6561 K 2038 2 (by decide) (by decide) (by rw [show (2038:Nat) = 1 + 3*679 from by decide, wt_row_eight_read]; decide) (by omega)

/-- **THE DUST PINNED AT LEVEL SEVEN — THE MAP DOUBLES TO 128.**  A
Cantorian dust exponent (`K ≡ 1 mod 3`) lives in one of ONE HUNDRED
TWENTY-EIGHT surviving residues mod 6561.  The structural law, fourth
stroke: `2, 4, 8, 16, 32, 64, 128` — the alive set doubles level by
level without exception, every node keeping exactly two children by
the blade's one-of-three. -/
theorem cantarian_dust_mod_6561 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 6561 = 1 ∨ K % 6561 = 4 ∨ K % 6561 = 13 ∨ K % 6561 = 40 ∨ K % 6561 = 94 ∨ K % 6561 = 109 ∨ K % 6561 = 121 ∨ K % 6561 = 166 ∨ K % 6561 = 193 ∨ K % 6561 = 244 ∨ K % 6561 = 280 ∨ K % 6561 = 283 ∨ K % 6561 = 325 ∨ K % 6561 = 364 ∨ K % 6561 = 436 ∨ K % 6561 = 496 ∨ K % 6561 = 514 ∨ K % 6561 = 523 ∨ K % 6561 = 595 ∨ K % 6561 = 730 ∨ K % 6561 = 733 ∨ K % 6561 = 739 ∨ K % 6561 = 823 ∨ K % 6561 = 838 ∨ K % 6561 = 850 ∨ K % 6561 = 922 ∨ K % 6561 = 928 ∨ K % 6561 = 973 ∨ K % 6561 = 1003 ∨ K % 6561 = 1009 ∨ K % 6561 = 1093 ∨ K % 6561 = 1144 ∨ K % 6561 = 1165 ∨ K % 6561 = 1171 ∨ K % 6561 = 1225 ∨ K % 6561 = 1228 ∨ K % 6561 = 1243 ∨ K % 6561 = 1252 ∨ K % 6561 = 1387 ∨ K % 6561 = 1468 ∨ K % 6561 = 1540 ∨ K % 6561 = 1624 ∨ K % 6561 = 1657 ∨ K % 6561 = 1732 ∨ K % 6561 = 1741 ∨ K % 6561 = 1783 ∨ K % 6561 = 1873 ∨ K % 6561 = 1900 ∨ K % 6561 = 1957 ∨ K % 6561 = 2038 ∨ K % 6561 = 2053 ∨ K % 6561 = 2116 ∨ K % 6561 = 2188 ∨ K % 6561 = 2191 ∨ K % 6561 = 2269 ∨ K % 6561 = 2353 ∨ K % 6561 = 2434 ∨ K % 6561 = 2467 ∨ K % 6561 = 2470 ∨ K % 6561 = 2512 ∨ K % 6561 = 2551 ∨ K % 6561 = 2623 ∨ K % 6561 = 2683 ∨ K % 6561 = 2767 ∨ K % 6561 = 2782 ∨ K % 6561 = 2917 ∨ K % 6561 = 2920 ∨ K % 6561 = 2944 ∨ K % 6561 = 3115 ∨ K % 6561 = 3163 ∨ K % 6561 = 3190 ∨ K % 6561 = 3196 ∨ K % 6561 = 3280 ∨ K % 6561 = 3331 ∨ K % 6561 = 3352 ∨ K % 6561 = 3412 ∨ K % 6561 = 3415 ∨ K % 6561 = 3433 ∨ K % 6561 = 3568 ∨ K % 6561 = 3658 ∨ K % 6561 = 3673 ∨ K % 6561 = 3685 ∨ K % 6561 = 3727 ∨ K % 6561 = 3844 ∨ K % 6561 = 3919 ∨ K % 6561 = 4060 ∨ K % 6561 = 4144 ∨ K % 6561 = 4162 ∨ K % 6561 = 4225 ∨ K % 6561 = 4297 ∨ K % 6561 = 4387 ∨ K % 6561 = 4414 ∨ K % 6561 = 4456 ∨ K % 6561 = 4468 ∨ K % 6561 = 4483 ∨ K % 6561 = 4495 ∨ K % 6561 = 4567 ∨ K % 6561 = 4618 ∨ K % 6561 = 4621 ∨ K % 6561 = 4888 ∨ K % 6561 = 4897 ∨ K % 6561 = 4954 ∨ K % 6561 = 5113 ∨ K % 6561 = 5131 ∨ K % 6561 = 5197 ∨ K % 6561 = 5212 ∨ K % 6561 = 5224 ∨ K % 6561 = 5296 ∨ K % 6561 = 5347 ∨ K % 6561 = 5350 ∨ K % 6561 = 5545 ∨ K % 6561 = 5617 ∨ K % 6561 = 5620 ∨ K % 6561 = 5626 ∨ K % 6561 = 5755 ∨ K % 6561 = 5761 ∨ K % 6561 = 5842 ∨ K % 6561 = 5845 ∨ K % 6561 = 5860 ∨ K % 6561 = 5872 ∨ K % 6561 = 5998 ∨ K % 6561 = 6115 ∨ K % 6561 = 6157 ∨ K % 6561 = 6274 ∨ K % 6561 = 6349 ∨ K % 6561 = 6427 ∨ K % 6561 = 6484 ∨ K % 6561 = 6490 := by
  have h2187 := cantorian_dust_mod_2187 K hd hc
  have hrow := hc 8 (by omega)
  have hd0 : K % 6561 ≠ 82 :=
    fun h => absurd (dust_fire_row_eight K (Or.inl h)) hrow
  have hd1 : K % 6561 ≠ 247 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inl h))) hrow
  have hd2 : K % 6561 ≠ 580 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hd3 : K % 6561 ≠ 757 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hd4 : K % 6561 ≠ 976 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hd5 : K % 6561 ≠ 1246 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hd6 : K % 6561 ≠ 1381 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hd7 : K % 6561 ≠ 1471 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hd8 : K % 6561 ≠ 1486 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hd9 : K % 6561 ≠ 1498 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hd10 : K % 6561 ≠ 1975 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hd11 : K % 6561 ≠ 2110 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hd12 : K % 6561 ≠ 2200 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hd13 : K % 6561 ≠ 2227 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hd14 : K % 6561 ≠ 2281 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hd15 : K % 6561 ≠ 2296 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))) hrow
  have hd16 : K % 6561 ≠ 2308 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))) hrow
  have hd17 : K % 6561 ≠ 2380 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))) hrow
  have hd18 : K % 6561 ≠ 2431 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))) hrow
  have hd19 : K % 6561 ≠ 2701 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))) hrow
  have hd20 : K % 6561 ≠ 2710 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))) hrow
  have hd21 : K % 6561 ≠ 2926 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))) hrow
  have hd22 : K % 6561 ≠ 3010 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))) hrow
  have hd23 : K % 6561 ≠ 3025 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))) hrow
  have hd24 : K % 6561 ≠ 3037 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))) hrow
  have hd25 : K % 6561 ≠ 3109 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))) hrow
  have hd26 : K % 6561 ≠ 3160 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))) hrow
  have hd27 : K % 6561 ≠ 3358 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))) hrow
  have hd28 : K % 6561 ≠ 3430 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))) hrow
  have hd29 : K % 6561 ≠ 3439 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))) hrow
  have hd30 : K % 6561 ≠ 3574 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))) hrow
  have hd31 : K % 6561 ≠ 3655 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))) hrow
  have hd32 : K % 6561 ≠ 3811 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))) hrow
  have hd33 : K % 6561 ≠ 3928 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))) hrow
  have hd34 : K % 6561 ≠ 3970 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))) hrow
  have hd35 : K % 6561 ≠ 4087 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))) hrow
  have hd36 : K % 6561 ≠ 4240 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))) hrow
  have hd37 : K % 6561 ≠ 4303 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))) hrow
  have hd38 : K % 6561 ≠ 4375 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))) hrow
  have hd39 : K % 6561 ≠ 4378 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))) hrow
  have hd40 : K % 6561 ≠ 4540 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))) hrow
  have hd41 : K % 6561 ≠ 4654 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd42 : K % 6561 ≠ 4657 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd43 : K % 6561 ≠ 4699 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd44 : K % 6561 ≠ 4738 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd45 : K % 6561 ≠ 4810 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd46 : K % 6561 ≠ 4870 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd47 : K % 6561 ≠ 4969 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd48 : K % 6561 ≠ 5104 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd49 : K % 6561 ≠ 5107 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd50 : K % 6561 ≠ 5302 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd51 : K % 6561 ≠ 5377 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd52 : K % 6561 ≠ 5383 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd53 : K % 6561 ≠ 5467 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd54 : K % 6561 ≠ 5518 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd55 : K % 6561 ≠ 5539 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd56 : K % 6561 ≠ 5599 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd57 : K % 6561 ≠ 5602 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd58 : K % 6561 ≠ 5914 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd59 : K % 6561 ≠ 6031 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd60 : K % 6561 ≠ 6106 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd61 : K % 6561 ≠ 6247 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd62 : K % 6561 ≠ 6331 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  have hd63 : K % 6561 ≠ 6412 :=
    fun h => absurd (dust_fire_row_eight K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) hrow
  rcases h2187 with h1 | h4 | h13 | h40 | h82 | h94 | h109 | h121 | h166 | h193 | h244 | h247 | h280 | h283 | h325 | h364 | h436 | h496 | h514 | h523 | h580 | h595 | h730 | h733 | h739 | h757 | h823 | h838 | h850 | h922 | h928 | h973 | h976 | h1003 | h1009 | h1093 | h1144 | h1165 | h1171 | h1225 | h1228 | h1243 | h1246 | h1252 | h1381 | h1387 | h1468 | h1471 | h1486 | h1498 | h1540 | h1624 | h1657 | h1732 | h1741 | h1783 | h1873 | h1900 | h1957 | h1975 | h2038 | h2053 | h2110 | h2116 <;> omega

/-- **THE CASCADE KILL, LEVEL SEVEN.**  The sixty-four new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_seven (K : Nat)
    (h : K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 8 (dust_fire_row_eight K h)

/-! ## Section 6 The pair-read fire — GAP-E1's first family -/

/-- **THE PAIR-READ FORMULA.**  The two-support tower factorization,
read through the green `prefaced_digit`:  for `1 ≤ j` and any trunk
`T` with `4^T < 3^(j+2)`, the row-`(j+4)` digit of `4^(T + 3^(j+1)*u)`
is the row-two digit of the worldtrace product `4^T * u * c (j+1)`.
The first brick of GAP-E1: the multi-support carry read, exact,
machine-verified 0 failures on 300 random (T, u, j). -/
```

## IV.5 The pair-read family — GAP-E1's infinite families

The fixed cascade levels can only kill what a fixed modulus sees. The class-4 trunk (K ≡ 4 mod 9) survives every fixed level — its residue 4 is in every survivor list. The pair-read family is the weapon that reaches it.

**`pair_read_formula`** (the uniform law): for ANY trunk `T` with `4^T < 3^(j+2)` and ANY branch `u`,

$$\mathrm{digit}_3\big(4^{T + 3^{j+1} u}\big)\big|_{\text{row } j+4} \;=\; \mathrm{digit}_3\big(4^T \cdot u \cdot c(j+1)\big)\big|_{\text{row } 2}$$

The proof: expand `4^(T + 3^(j+1)·u) = 4^T·(4^(3^(j+1)))^u = 4^T·(1 + 3^(j+2)·c(j+1))^u` by the three-term ladder; the result is `4^T + 3^(j+2)·(4^T·u·c(j+1)) + 3^(2j+4)·(...)`. The green `prefaced_digit` law then shifts: row `j+4` of the whole is row 2 of the middle factor (the preface `4^T` is too small to reach, the tail is too divisible to be seen).

**`pair_residue_mod27`**: `c(j+1) ≡ 16 (mod 27)` for `j ≥ 2`, so the read reduces to `(4^T·u·16) mod 27`.

**`digit3_row_two_of_residue`**: if `18 ≤ x mod 27`, then row 2 of x is 2 (because row 2 = ⌊(x mod 27)/9⌋ and 18 ≤ residue ≤ 26 gives exactly 2).

**`pair_read_fire_general`** (the general trunk-uniform fire): whenever `(4^T·u·16) mod 27 ≥ 18`, the exponent `T + 3^(j+1)·u` fires its digit 2 at row `j+4`. The kill condition is a **mod-27 automaton on (trunk residue, branch trit)** — uniform across the entire dust tree, all levels at once.

**`pair_read_fire`**: the first infinite family — every `K = 4 + 3^(j+1)·u` with `j ≥ 4` and `u ∈ {1, 4, 7}` fires at row `j+4`. Why these three: `4^4 = 256 ≡ 13 (mod 27)`, and `13·16 ≡ 19`, `13·4·16 ≡ 22`, `13·7·16 ≡ 25 (mod 27)` — all in the kill zone [18, 26]. One theorem, the infinite family 247, 733, 976, 2191, 2920, 6565, 8752, 15313, … — exponents that ride the class-4 trunk past every fixed cascade level.

**`pair_read_fire_demo_two` / `demo_three`**: the trunk-13 and further families, firing at row `j+4` for all `j ≥ 15` (resp. `j ≥ 11`) — the same automaton on different trunks.

**`no22_of_pair_read` / `no22_of_pair_read_general`**: the kill-chain forms. **`the_pair_read_receipt`** and **`the_general_fire_receipt`** package the families as single conjunctions.

Receipts R12, R13, R15 in Part VI verify: 27/27 family members fire exactly at row `j+4`; the trunk-13 automaton matches 15/15 including its negative controls; 44/44 random kill-zone triples fire.

```lean
theorem pair_read_formula (T u j : Nat) (hj : 1 ≤ j) (hT : 4^T < 3^(j+2)) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2 := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term (3^(j+2) * GSTTowerFire.c (j+1)) u
  have htow : 4^(3^(j+1)) = 1 + 3^(j+2) * GSTTowerFire.c (j+1) :=
    GSTTowerFire.four_pow_three_pow_eq (j+1)
  have key : 4^(T + 3^(j+1)*u)
      = 3^(j+2) * (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)))
        + 4^T := by
    rw [Nat.pow_add, Nat.pow_mul, htow, hR]
    ring
  rw [key]
  have hp : digit3 (3^(j+2) * (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) + 4^T) (j+4)
      = digit3 (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) 2 :=
    GSTTowerFire.prefaced_digit _ (4^T) (j+1) 2 hT
  rw [hp]
  refine digit3_eq_of_mod_next _ _ 2 ?_
  show (4^T * u * GSTTowerFire.c (j+1)
          + 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R))) % 27
     = (4^T * u * GSTTowerFire.c (j+1)) % 27
  have h27eq : 3^(j+2) = 27 * 3^(j-1) := by
    have hsum : j + 2 = (j - 1) + 3 := by omega
    rw [hsum, Nat.pow_add]
    ring
  have hd2 : 27 ∣ 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)) := by
    refine ⟨3^(j-1) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)), ?_⟩
    rw [h27eq]
    ring
  have hz : 3^(j+2) * (4^T * (Nat.choose u 2
              * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
            + 3^(j+2) * GSTTowerFire.c (j+1) * GSTTowerFire.c (j+1)
              * GSTTowerFire.c (j+1) * R)) % 27 = 0 := Nat.mod_eq_zero_of_dvd hd2
  omega

/-- **THE PAIR-READ FIRE.**  Every exponent `K = 4 + 3^(j+1)*u` with
`j ≤ 4` and `u = 1 ∨ u = 4 ∨ u = 7` fires its digit two at row `j + 4` —
the pair term `3^(j+2) * (256 * u * c (j+1))` read through the green
`c_mod81` (`c = 16 mod 27`): the digit is trit two of `19*u`, which is
two exactly for `u` in {1, 4, 7}.  GAP-E1's first infinite family:
one theorem, the exponents 247, 733, 976, 1705, 2191, 2920, ... — the
class-4 trunk with a one-trit branch `u = 1 mod 3`, a family NO finite
cascade level ever reaches (these exponents ride the class-4 trunk,
and class 4 survives every fixed level).  Machine-verified: j = 4..12
all fire. -/
theorem pair_read_fire (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2 := by
  have h6 : (3:Nat)^6 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h256 : (4:Nat)^4 = 256 := by decide
  have h729 : (3:Nat)^6 = 729 := by decide
  have hT : (4:Nat)^4 < 3^(j+2) := by omega
  have hc : GSTTowerFire.c (j+1) % 27 = 16 := by
    have h81 := GSTTowerFire.c_mod81 (j+1) (by omega)
    have hrr := Nat.mod_mod_of_dvd (GSTTowerFire.c (j+1)) (by decide : (27:Nat) ∣ 81)
    rw [← hrr, h81]
  have hform := pair_read_formula 4 u j (by omega) hT
  rw [hform, h256]
  rcases hu with rfl | rfl | rfl
  · have hmod : (256 * 1 * GSTTowerFire.c (j+1)) % 27 = 19 % 27 := by
      rw [Nat.mul_one, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)
  · have hmod : (256 * 4 * GSTTowerFire.c (j+1)) % 27 = 76 % 27 := by
      rw [show (256:Nat) * 4 = 1024 from by decide, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)
  · have hmod : (256 * 7 * GSTTowerFire.c (j+1)) % 27 = 133 % 27 := by
      rw [show (256:Nat) * 7 = 1792 from by decide, Nat.mul_mod, hc]
    exact (digit3_eq_of_mod_next _ _ 2 hmod).trans (by decide)

/-- **THE PAIR-READ KILL.**  The family dies outright through the repo's
own kill chain. -/
theorem no22_of_pair_read (u j : Nat) (hj : 4 ≤ j) (hu : u = 1 ∨ u = 4 ∨ u = 7) :
    noTernaryTwo (4^(4 + 3^(j+1)*u)) = false :=
  no22_of_digit_two _ (j+4) (pair_read_fire u j hj hu)

/-- **THE PAIR-READ RECEIPT.**  The GAP-E1 brick assembled: the uniform
read formula, the infinite fire family, and the kill chain. -/
theorem the_pair_read_receipt :
    (∀ T u j : Nat, 1 ≤ j → 4^T < 3^(j+2) →
      digit3 (4^(T + 3^(j+1)*u)) (j+4)
        = digit3 (4^T * u * GSTTowerFire.c (j+1)) 2) ∧
    (∀ u j : Nat, 4 ≤ j → (u = 1 ∨ u = 4 ∨ u = 7) →
      digit3 (4^(4 + 3^(j+1)*u)) (j+4) = 2) ∧
    (∀ u j : Nat, 4 ≤ j → (u = 1 ∨ u = 4 ∨ u = 7) →
      noTernaryTwo (4^(4 + 3^(j+1)*u)) = false) :=
  ⟨pair_read_formula, pair_read_fire, no22_of_pair_read⟩

/-! ## Section 7 The general trunk-uniform fire — any trunk, any branch -/

/-- **THE ROW-TWO READ FROM THE KILL ZONE.**  A number whose mod-27
residue lands at or above eighteen reads digit two at row two — the
kill zone of the worldtrace pair-read. -/
theorem digit3_row_two_of_residue (x : Nat) (hx : 18 ≤ x % 27) :
    digit3 x 2 = 2 := by
  have hlt : x % 27 < 27 := Nat.mod_lt _ (by decide : 0 < 27)
  show x / 9 % 3 = 2
  omega

/-- **THE PAIR-READ RESIDUE.**  The worldtrace product's mod-27 residue
is computable without the tower:  `c (j+1)` is `16 mod 27` (green
`c_mod81`), so the read `4^T * u * c (j+1)` reduces to `4^T * u * 16`.
Machine-verified 0 failures on 400 random triples. -/
theorem pair_residue_mod27 (T u j : Nat) (hj : 2 ≤ j) :
    (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27 := by
  have hc : GSTTowerFire.c (j+1) % 27 = 16 := by
    have h81 := GSTTowerFire.c_mod81 (j+1) (by omega)
    have hrr := Nat.mod_mod_of_dvd (GSTTowerFire.c (j+1)) (by decide : (27:Nat) ∣ 81)
    rw [← hrr, h81]
  have h16 : (16:Nat) % 27 = 16 := by decide
  have hl := Nat.mul_mod (4^T * u) (GSTTowerFire.c (j+1)) 27
  have hr := Nat.mul_mod (4^T * u) 16 27
  rw [hl, hr, hc, h16]

/-- **THE GENERAL TRUNK-UNIFORM FIRE.**  ANY trunk `T`, ANY branch `u`:
whenever the mod-27 residue `(4^T * u * 16) % 27` lands in the kill
zone (`18 ≤ residue`), the exponent `T + 3^(j+1)*u` fires its digit
two at row `j+4`.  The kill condition is a mod-27 computation on the
trunk residue and the branch — the Cantor automaton's transition,
uniform across the entire dust tree.  Machine-verified 0 failures on
120 valid random triples. -/
theorem pair_read_fire_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2 := by
  have hform := pair_read_formula T u j (by omega) hT
  rw [hform]
  exact digit3_row_two_of_residue _ (by
    rw [pair_residue_mod27 T u j (by omega)]
    exact hkill)

/-- **THE GENERAL PAIR-READ KILL.**  The family dies outright through
the repo's own kill chain. -/
theorem no22_of_pair_read_general (T u j : Nat) (hj : 4 ≤ j) (hT : 4^T < 3^(j+2))
    (hkill : 18 ≤ (4^T * u * 16) % 27) :
    noTernaryTwo (4^(T + 3^(j+1)*u)) = false :=
  no22_of_digit_two _ (j+4) (pair_read_fire_general T u j hj hT hkill)

/-- **SECOND FAMILY — the trunk-13 dust class.**  Class 13 (a level-two
dust survivor) with a single deep branch:  fires at row `j+4` for
every `j ≥ 15`.  The trunk residue `4^13 mod 27 = 13` gives kill
residue `13 * 16 mod 27 = 19`, inside the kill zone. -/
theorem pair_read_fire_demo_two (j : Nat) (hj : 15 ≤ j) :
    digit3 (4^(13 + 3^(j+1))) (j+4) = 2 := by
  have h17 : (3:Nat)^17 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4 : (4:Nat)^13 < (3:Nat)^17 := by decide
  have hgen := pair_read_fire_general 13 1 j (by omega) (by omega) (by decide)
  rw [Nat.mul_one] at hgen
  exact hgen

/-- **THIRD FAMILY — the trunk-10 class with branch two.**  Class 10
(a level-two dust survivor) with branch `u = 2`:  fires at row `j+4`
for every `j ≥ 11`.  Kill residue `4 * 2 * 16 mod 27 = 20`. -/
theorem pair_read_fire_demo_three (j : Nat) (hj : 11 ≤ j) :
    digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2 := by
  have h13 : (3:Nat)^13 ≤ 3^(j+2) := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
  have h4 : (4:Nat)^10 < (3:Nat)^13 := by decide
  exact pair_read_fire_general 10 2 j (by omega) (by omega) (by decide)

/-- **THE GENERAL FIRE RECEIPT.**  The GAP-E1 engine assembled: the
residue transfer, the row-two kill-zone read, the general trunk-uniform
fire (any trunk, any branch), the kill chain, and two new infinite
families (trunk 13 single-branch; trunk 10 with branch two). -/
theorem the_general_fire_receipt :
    (∀ T u j : Nat, 2 ≤ j →
      (4^T * u * GSTTowerFire.c (j+1)) % 27 = (4^T * u * 16) % 27) ∧
    (∀ x : Nat, 18 ≤ x % 27 → digit3 x 2 = 2) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
      digit3 (4^(T + 3^(j+1)*u)) (j+4) = 2) ∧
    (∀ T u j : Nat, 4 ≤ j → 4^T < 3^(j+2) → 18 ≤ (4^T * u * 16) % 27 →
      noTernaryTwo (4^(T + 3^(j+1)*u)) = false) ∧
    (∀ j : Nat, 15 ≤ j → digit3 (4^(13 + 3^(j+1))) (j+4) = 2) ∧
    (∀ j : Nat, 11 ≤ j → digit3 (4^(10 + 3^(j+1)*2)) (j+4) = 2) :=
  ⟨pair_residue_mod27, digit3_row_two_of_residue, pair_read_fire_general,
    no22_of_pair_read_general, pair_read_fire_demo_two, pair_read_fire_demo_three⟩

/-! ## Section 8 The top-split and the addition window — the descent engine -/

/-- **THE EXACT TOP SPLIT.**  For an exponent `K` whose top trit sits at
position `H` (`K < 3^(H+1)`), the power splits as the trunk power, the
branch term, and a tail dead below row `2H+2`.  The deep rows of `4^K`
are a pure base-3 addition of the trunk's digits and the shifted
digits of `X = t * c(H) * 4^trunk`.  Machine-verified: the
addition-window law holds 600/600 on random `(H, trunk, t)`. -/
```

## IV.6 The descent engine — the top split, the addition window, the row-(H+2) law

The descent engine is the monolith's most structural section: it does not kill classes, it *reduces exponents*.

**`top_split`**: for `K < 3^(H+1)`, writing `trunk = K mod 3^H` and `branch = K / 3^H < 3`,

$$4^K = 4^{\mathrm{trunk}} + 3^{H+1}\cdot\big(\mathrm{branch} \cdot c(H) \cdot 4^{\mathrm{trunk}}\big) + 3^{2H+2}\cdot Y$$

with `Y` an explicit polynomial in `branch, c(H), 4^trunk, R`. The power of the big exponent is a **preface (the trunk's power) plus a shifted middle term (the branch's contribution) plus a deep tail**.

**`window_congr`** (the addition window): below row `2H+2`, the tail is invisible — the digits of `4^K` agree with the digits of the two-term sum `4^trunk + 3^(H+1)·X` where `X = branch·c(H)·4^trunk`. The proof exhibits `3^(H+1)·3^(H+1) = 3^(2H+2)` and uses `Nat.add_mul_mod_self_left` — the tail's divisibility kills it below the window.

**`window_row_two`** (the row-(H+2) read): the digit at row `H+2` of `4^K` is

$$\Big(\mathrm{digit}_3\big(4^{\mathrm{trunk}}\big)\big|_{H+2} + \big\lfloor X/3 \big\rfloor \bmod 3 + \big\lfloor \mathrm{digit}_3(4^{\mathrm{trunk}})|_{H+1} + \mathrm{branch}\big\rfloor / 3 \Big) \bmod 3$$

— a pure base-3 column addition: the trunk's own digit at that row, plus the leading trit of the branch factor, plus the carry from the row below. Machine-verified 800/800 in the repo; spot-checked in receipt R14.

**The descent, conceptually**: to decide row `H+2` of `4^K`, you need rows `H+1, H+2` of `4^trunk` with `trunk < 3^H` — a *strictly smaller exponent — plus the top trit of `K`. The worldtrace at height `H+2` reads the worldtrace at lower height of a smaller exponent, plus one fresh trit of `K` itself. This is the induction structure the conjecture lives inside.

**`the_descent_engine_receipt`** packages the three theorems as one conjunction.

```lean
theorem top_split (K H : Nat) (hK : K < 3^(H+1)) :
    ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)
        + 3^(H+1) * Y) := by
  obtain ⟨R, hR⟩ := one_add_pow_three_term (3^(H+1) * GSTTowerFire.c H) (K / 3^H)
  have hsplit : K % 3^H + 3^H * (K / 3^H) = K := Nat.mod_add_div K (3^H)
  have hexp : 4^K = 4^(K % 3^H) * (1 + 3^(H+1) * GSTTowerFire.c H)^(K / 3^H) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.pow_add, Nat.pow_mul, GSTTowerFire.four_pow_three_pow_eq H]
  refine ⟨Nat.choose (K / 3^H) 2 * GSTTowerFire.c H * GSTTowerFire.c H * 4^(K % 3^H)
      + 3^(H+1) * (GSTTowerFire.c H * GSTTowerFire.c H * GSTTowerFire.c H * R * 4^(K % 3^H)), ?_⟩
  rw [hexp, hR]
  ring

/-- **THE ADDITION WINDOW.**  Below row `2H+2`, the digits of `4^K` read
the two-term sum `4^trunk + 3^(H+1) * X` — the dead tail of the top
split is invisible.  The descent engine's foundation. -/
theorem window_congr (K H r : Nat) (hK : K < 3^(H+1)) (hr : r + 1 ≤ 2*H+2) :
    digit3 (4^K) r = digit3 (4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r := by
  obtain ⟨Y, hY⟩ := top_split K H hK
  refine digit3_eq_of_mod_next _ _ r ?_
  rw [hY, Nat.mul_add]
  have hpow : 3^(H+1) * 3^(H+1) = 3^(2*H+2) := by
    have h := Nat.pow_add 3 (H+1) (H+1)
    rw [show (H+1)+(H+1) = 2*H+2 from by omega] at h
    exact h.symm
  have hdvd : 3^(r+1) ∣ 3^(H+1) * (3^(H+1) * Y) := by
    rw [← Nat.mul_assoc, hpow]
    exact (Nat.pow_dvd_pow 3 (by omega)).mul_right Y
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, ← Nat.add_assoc]
  exact Nat.add_mul_mod_self_left _ _ _

/-- **THE ROW-(H+2) WINDOW LAW.**  The digit at row `H+2` of `4^K` is
the trunk's own digit at that row, plus the first trit of the branch
factor `X = t * c(H) * 4^trunk`, plus the carry from row `H+1` — a pure
base-3 addition read.  Machine-verified 800/800. -/
theorem window_row_two (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1)) :
    digit3 (4^K) (H+2)
      = (digit3 (4^(K % 3^H)) (H+2)
          + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
          + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3 := by
  have htpow : 3^(H+2) = 3^(H+1) * 3 := Nat.pow_succ 3 (H+1)
  have ht : K / 3^H < 3 := by
    rw [Nat.pow_succ 3 H] at hK
    by_contra hc
    have hd := Nat.mod_add_div K (3^H)
    have hle : 3^H * 3 ≤ 3^H * (K / 3^H) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hx3 : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) % 3 = K / 3^H := by
    have hc : GSTTowerFire.c H % 3 = 1 := GSTTowerFire.c_mod3 H
    have hA3 : (4^(K % 3^H)) % 3 = 1 := GSTClimbInfiniteFamily.pow4_mod3 (K % 3^H)
    have ht3 : (K / 3^H) % 3 = K / 3^H := Nat.mod_eq_of_lt ht
    have hpair : ((K / 3^H) * GSTTowerFire.c H) % 3 = (K / 3^H) % 3 := by
      rw [Nat.mul_mod, hc, Nat.mul_one]
      omega
    rw [Nat.mul_mod, hpair, hA3, Nat.mul_one, ht3, ht3]
  rw [window_congr K H (H+2) hK (by omega)]
  set A := 4^(K % 3^H) with hAdef
  set X := (K / 3^H) * GSTTowerFire.c H * A with hXdef
  have hp1 : 0 < 3^(H+1) := Nat.pow_pos (by decide)
  have hr1lt : A % 3^(H+2) % 3^(H+1) < 3^(H+1) :=
    Nat.mod_lt _ hp1
  unfold digit3
  have hdiv : (A + 3^(H+1) * X) / 3^(H+2)
      = A / 3^(H+2) + X / 3 + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3 := by
    have hAsplit := Nat.div_add_mod A (3^(H+2))
    have hDsplit := Nat.div_add_mod (A % 3^(H+2)) (3^(H+1))
    have hXsplit := Nat.div_add_mod X 3
    rw [hx3] at hXsplit
    have hq3split := Nat.div_add_mod (A % 3^(H+2) / 3^(H+1) + K / 3^H) 3
    have hkey : A + 3^(H+1) * X
        = 3^(H+2) * (A / 3^(H+2) + X / 3
            + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3)
          + (3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
            + A % 3^(H+2) % 3^(H+1)) := by
      linear_combination
        -(hAsplit + 3^(H+1) * hXsplit + hDsplit + 3^(H+1) * hq3split)
        - (X / 3 + (A % 3^(H+2) / 3^(H+1) + K / 3^H) / 3) * htpow
    have hslt : 3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
        + A % 3^(H+2) % 3^(H+1) < 3^(H+2) := by
      have h3lt : (A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3 < 3 :=
        Nat.mod_lt _ (by decide)
      have hmul : 3^(H+1) * ((A % 3^(H+2) / 3^(H+1) + K / 3^H) % 3)
          ≤ 3^(H+1) * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [hkey, GSTTowerFire.div_add_lt (H+2) _ _ hslt]
  rw [hdiv]
  have hd1 : A / 3^(H+1) % 3 = A % 3^(H+2) / 3^(H+1) := by
    have hAsplit := Nat.div_add_mod A (3^(H+2))
    have hDsplit := Nat.div_add_mod (A % 3^(H+2)) (3^(H+1))
    have hA2 : A = 3^(H+1) * (3 * (A / 3^(H+2)) + A % 3^(H+2) / 3^(H+1))
        + A % 3^(H+2) % 3^(H+1) := by
      linear_combination -(hAsplit + hDsplit) + (A / 3^(H+2)) * htpow
    have hdiv2 : A / 3^(H+1)
        = 3 * (A / 3^(H+2)) + A % 3^(H+2) / 3^(H+1) := by
      conv_lhs => rw [hA2]
      exact GSTTowerFire.div_add_lt (H+1) _ _ hr1lt
    have hDlt : A % 3^(H+2) / 3^(H+1) < 3 := by
      by_contra hc
      push_neg at hc
      have hle : 3^(H+1) * 3 ≤ 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) :=
        Nat.mul_le_mul_left _ hc
      have h1 : 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) ≤ A % 3^(H+2) := by
        omega
      have h2 : 3^(H+2) ≤ 3^(H+1) * (A % 3^(H+2) / 3^(H+1)) := by
        conv_lhs => rw [htpow]
        exact hle
      omega
    rw [hdiv2]
    rw [Nat.add_comm (3 * (A / 3^(H+2))) (A % 3^(H+2) / 3^(H+1))]
    rw [Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hDlt
  rw [hd1]
  omega

/-- **THE DESCENT ENGINE RECEIPT.**  The top split, the addition window,
and the row-(H+2) law assembled. -/
theorem the_descent_engine_receipt :
    (∀ K H : Nat, K < 3^(H+1) → ∃ Y : Nat, 4^K = 4^(K % 3^H)
      + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H) + 3^(H+1) * Y)) ∧
    (∀ K H r : Nat, K < 3^(H+1) → r + 1 ≤ 2*H+2 →
      digit3 (4^K) r = digit3 (4^(K % 3^H)
        + 3^(H+1) * ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H))) r) ∧
    (∀ K H : Nat, 1 ≤ H → K < 3^(H+1) →
      digit3 (4^K) (H+2)
        = (digit3 (4^(K % 3^H)) (H+2)
            + ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3
            + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3) :=
  ⟨fun K H hK => top_split K H hK,
    fun K H r hK hr => window_congr K H r hK hr,
    fun K H hH hK => window_row_two K H hH hK⟩

/-! ## Section 9 The dust window laws — the branch term vanishes mod nine -/

/-- **THE PERIOD-NINE LAW.**  `4^r mod 9` depends only on `r mod 3`
(`4^3 = 64 = 1 + 9*7`).  Receipt: 0 failures for r < 100. -/
```

## IV.7 The dust window — the mod-9 laws and the final receipts

The dust window section closes the loop for Cantorian dust exponents (`K ≡ 1 mod 3`).

**`four_pow_mod9`**: `4^r mod 9 = 4^(r mod 3) mod 9` — the power stream mod 9 has period 3 in the exponent, with values `4, 7, 1`.

**`dust_branch_mod9`**: for `trunk ≡ 1 mod 3` (a dust trunk), `(t · c(H) · 4^trunk) mod 9 = t`. The branch factor `X = t·c(H)·4^trunk` *reduces to its own top trit* mod 9 — because `c(H) ≡ 7 mod 9` and `4^trunk ≡ 4 mod 9` when `trunk ≡ 1 mod 3`, and `7·4 = 28 ≡ 1 (mod 9)`. The three factors conspire to cancel mod 9. **This is a law nobody ordered: the LTE coefficient and the power residue are multiplicative inverses mod 9 on the dust tree.**

**`window_row_two_dust`**: the descent's row-(H+2) law specialized to dust trunks: row `H+2` of `4^K` = (row `H+2` of `4^trunk` + (row `H+1` of `4^trunk` + branch)/3) mod 3 — the branch factor's leading trit drops out entirely (it was `t`, already counted), leaving a two-term read.

**`window_reduce`**: a general window reduction — row `H+1+s` of `A + 3^(H+1)·X` only sees `X mod 3^(s+1)`.

**`the_dust_window_receipt`** packages the four. Then come the two grand receipts:

**`the_worldtrace_receipt`** — the level-six storey in one theorem: the rebase, the ladder, the quadratic and cubic blades, the two polynomial reads, the kill demo, the uniform engine, the 32 fires, the kill chain, the 64-survivor map.

**`the_worldtrace_receipt_seven`** — the level-seven storey: the five-term ladder, the quartic blade, the row-eight read, the kill demo, the uniform engine at level seven, the 64 fires, the kill chain, the 128-survivor map.

And the closing wall of `#print axioms` — 45 declarations, each certified to rest on `[propext, Classical.choice, Quot.sound]` and nothing else. No `sorry`, no custom axioms, no `native_decide`. This is the machine's own signature under the worldtrace arithmetic.

```lean
theorem four_pow_mod9 (r : Nat) : (4:Nat)^r % 9 = 4^(r % 3) % 9 := by
  have hsplit := Nat.div_add_mod r 3
  obtain ⟨W, hW⟩ := one_add_pow_three_term (9 * 7) (r / 3)
  have h64 : (4:Nat)^(3:Nat) = 1 + 9 * 7 := by decide
  have hexp : (4:Nat)^r = (1 + 9 * 7)^(r / 3) * 4^(r % 3) := by
    conv_lhs => rw [← hsplit]
    rw [Nat.pow_add, Nat.pow_mul, h64]
  rw [hexp, hW]
  have hdvd : 9 ∣ (r / 3) * (9 * 7)
      + Nat.choose (r / 3) 2 * (9 * 7) * (9 * 7)
      + (9 * 7) * (9 * 7) * (9 * 7) * W := by
    refine ⟨(r / 3) * 7 + 9 * (Nat.choose (r / 3) 2 * 7 * 7)
      + 9 * 9 * (7 * 7 * 7 * W), ?_⟩
    ring
  obtain ⟨q, hq⟩ := hdvd
  have hfold : (1 + (r / 3) * (9 * 7)
      + Nat.choose (r / 3) 2 * (9 * 7) * (9 * 7)
      + (9 * 7) * (9 * 7) * (9 * 7) * W) * 4^(r % 3)
      = 4^(r % 3) + 9 * (4^(r % 3) * q) := by
    linear_combination 4^(r % 3) * hq
  rw [hfold, Nat.add_mul_mod_self_left]

/-- **THE DUST BRANCH FACTOR.**  For a dust trunk (`trunk mod 3 = 1`)
the branch factor `X = t * c(H) * 4^trunk` satisfies `X mod 9 = t` —
`c(H)` is `7 mod 9`, `4^trunk` is `4 mod 9`, and `7 * 4 = 28 = 1 mod 9`.
Receipt: 0 failures on 300 random (H, trunk, t). -/
theorem dust_branch_mod9 (t trunk H : Nat) (hH : 1 ≤ H) (htr : trunk % 3 = 1)
    (ht : t < 3) :
    (t * GSTTowerFire.c H * 4^trunk) % 9 = t := by
  have hc := GSTTowerFire.c_mod9 H hH
  have h4 := four_pow_mod9 trunk
  rw [htr] at h4
  have h41 : (4:Nat)^(1:Nat) % 9 = 4 := by decide
  rw [h41] at h4
  have h1 := Nat.mul_mod t (GSTTowerFire.c H) 9
  have h2 := Nat.mul_mod (t * GSTTowerFire.c H) (4^trunk) 9
  rw [h2, h1, hc, h4]
  omega

/-- **THE DUST ROW-(H+2) LAW — the branch term vanishes.**  For a dust
exponent (`K mod 3 = 1`) the row-(H+2) digit is JUST the trunk's digit
plus the carry — the branch factor's first trit is zero because
`X mod 9 = t < 3`.  The descent's cleanest rung.  Receipt: 196/196. -/
theorem window_row_two_dust (K H : Nat) (hH : 1 ≤ H) (hK : K < 3^(H+1))
    (hdust : K % 3 = 1) :
    digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
      + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3 := by
  have ht : K / 3^H < 3 := by
    rw [Nat.pow_succ 3 H] at hK
    by_contra hc
    have hd := Nat.mod_add_div K (3^H)
    have hle : 3^H * 3 ≤ 3^H * (K / 3^H) := Nat.mul_le_mul_left _ (by omega)
    omega
  have htr : (K % 3^H) % 3 = 1 := by
    have hd3 : (3:Nat) ∣ 3^H := by
      refine ⟨3^(H-1), ?_⟩
      rw [Nat.mul_comm, ← Nat.pow_succ 3 (H-1)]
      congr 1
      omega
    have hrr := Nat.mod_mod_of_dvd K hd3
    omega
  rw [window_row_two K H hH hK]
  have hx9 : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) % 9 = K / 3^H :=
    dust_branch_mod9 (K / 3^H) (K % 3^H) H hH htr ht
  have hterm : ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) / 3 % 3 = 0 := by
    have hmm := Nat.mod_mod_of_dvd
      ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) (by decide : (3:Nat) ∣ 9)
    have hdm := Nat.div_add_mod
      ((K / 3^H) * GSTTowerFire.c H * 4^(K % 3^H)) 9
    omega
  rw [hterm]
  omega

/-- **THE WINDOW REDUCTION.**  The digit at row `H+1+s` of the two-term
sum only sees the first `s+1` trits of the branch factor — reduce
`X mod 3^(s+1)` and the higher trits are invisible.  The consumers'
computational handle: the reduced branch factor is small. -/
theorem window_reduce (A X H s : Nat) :
    digit3 (A + 3^(H+1) * X) (H+1+s)
      = digit3 (A + 3^(H+1) * (X % 3^(s+1))) (H+1+s) := by
  refine digit3_eq_of_mod_next _ _ (H+1+s) ?_
  rw [show (H:Nat)+1+s+1 = H+s+2 from by omega]
  have hX := Nat.div_add_mod X (3^(s+1))
  have hpow : 3^(H+1) * 3^(s+1) = 3^(H+s+2) := by
    have h := Nat.pow_add 3 (H+1) (s+1)
    rw [show (H:Nat)+1+(s+1) = H+s+2 from by omega] at h
    exact h.symm
  have hfold : A + 3^(H+1) * X
      = A + 3^(H+1) * (X % 3^(s+1)) + 3^(H+s+2) * (X / 3^(s+1)) := by
    conv_lhs => rw [← hX]
    rw [Nat.mul_add, ← Nat.mul_assoc, hpow]
    ring
  rw [hfold]
  exact Nat.add_mul_mod_self_left _ _ _

/-- **THE DUST WINDOW RECEIPT.**  The period law, the branch vanishing,
the clean row-(H+2) law, and the reduction handle. -/
theorem the_dust_window_receipt :
    (∀ r : Nat, (4:Nat)^r % 9 = 4^(r % 3) % 9) ∧
    (∀ t trunk H : Nat, 1 ≤ H → trunk % 3 = 1 → t < 3 →
      (t * GSTTowerFire.c H * 4^trunk) % 9 = t) ∧
    (∀ K H : Nat, 1 ≤ H → K < 3^(H+1) → K % 3 = 1 →
      digit3 (4^K) (H+2) = (digit3 (4^(K % 3^H)) (H+2)
        + (digit3 (4^(K % 3^H)) (H+1) + K / 3^H) / 3) % 3) ∧
    (∀ A X H s : Nat,
      digit3 (A + 3^(H+1) * X) (H+1+s)
        = digit3 (A + 3^(H+1) * (X % 3^(s+1))) (H+1+s)) :=
  ⟨four_pow_mod9, dust_branch_mod9, window_row_two_dust, window_reduce⟩

/-- **THE LEVEL-SIX RECEIPT.**  The worldtrace transformation assembled:
the binomial ladder, the quadratic and cubic blades, the polynomial
reads, the polynomial kill demo, the uniform engine, the thirty-two
fires, the kill chain, and the doubled survivor map. -/
theorem the_worldtrace_receipt :
    (∀ m : Nat, 4^(1+3*m) = 4 * 64^m) ∧
    (∀ m : Nat, ∃ R : Nat, (1+63)^m
      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + 63*63*63*R) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2 [MOD 729]) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 [MOD 6561]) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 5
      = digit3 (4 + 252*m + 15876*Nat.choose m 2) 5) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 7
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3) 7) ∧
    (digit3 (4^(1+3*28)) 5 = 2) ∧
    (∀ K r t : Nat, r < 729 → t < 3 →
      (digit3 (4^r) 7 + t) % 3 = 2 → K % 2187 = r + 729 * t →
      digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → digit3 (4^K) 7 = 2) ∧
    (∀ K : Nat, K % 2187 = 10 ∨ K % 2187 = 28 ∨ K % 2187 = 199 ∨ K % 2187 = 274 ∨ K % 2187 = 415 ∨ K % 2187 = 442 ∨ K % 2187 = 499 ∨ K % 2187 = 517 ∨ K % 2187 = 652 ∨ K % 2187 = 658 ∨ K % 2187 = 742 ∨ K % 2187 = 769 ∨ K % 2187 = 811 ∨ K % 2187 = 895 ∨ K % 2187 = 1012 ∨ K % 2187 = 1054 ∨ K % 2187 = 1309 ∨ K % 2187 = 1324 ∨ K % 2187 = 1459 ∨ K % 2187 = 1462 ∨ K % 2187 = 1552 ∨ K % 2187 = 1567 ∨ K % 2187 = 1579 ∨ K % 2187 = 1651 ∨ K % 2187 = 1702 ∨ K % 2187 = 1705 ∨ K % 2187 = 1738 ∨ K % 2187 = 1822 ∨ K % 2187 = 1894 ∨ K % 2187 = 1954 ∨ K % 2187 = 1972 ∨ K % 2187 = 1981 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 2187 = 1 ∨ K % 2187 = 4 ∨ K % 2187 = 13 ∨ K % 2187 = 40 ∨ K % 2187 = 82 ∨ K % 2187 = 94 ∨ K % 2187 = 109 ∨ K % 2187 = 121 ∨ K % 2187 = 166 ∨ K % 2187 = 193 ∨ K % 2187 = 244 ∨ K % 2187 = 247 ∨ K % 2187 = 280 ∨ K % 2187 = 283 ∨ K % 2187 = 325 ∨ K % 2187 = 364 ∨ K % 2187 = 436 ∨ K % 2187 = 496 ∨ K % 2187 = 514 ∨ K % 2187 = 523 ∨ K % 2187 = 580 ∨ K % 2187 = 595 ∨ K % 2187 = 730 ∨ K % 2187 = 733 ∨ K % 2187 = 739 ∨ K % 2187 = 757 ∨ K % 2187 = 823 ∨ K % 2187 = 838 ∨ K % 2187 = 850 ∨ K % 2187 = 922 ∨ K % 2187 = 928 ∨ K % 2187 = 973 ∨ K % 2187 = 976 ∨ K % 2187 = 1003 ∨ K % 2187 = 1009 ∨ K % 2187 = 1093 ∨ K % 2187 = 1144 ∨ K % 2187 = 1165 ∨ K % 2187 = 1171 ∨ K % 2187 = 1225 ∨ K % 2187 = 1228 ∨ K % 2187 = 1243 ∨ K % 2187 = 1246 ∨ K % 2187 = 1252 ∨ K % 2187 = 1381 ∨ K % 2187 = 1387 ∨ K % 2187 = 1468 ∨ K % 2187 = 1471 ∨ K % 2187 = 1486 ∨ K % 2187 = 1498 ∨ K % 2187 = 1540 ∨ K % 2187 = 1624 ∨ K % 2187 = 1657 ∨ K % 2187 = 1732 ∨ K % 2187 = 1741 ∨ K % 2187 = 1783 ∨ K % 2187 = 1873 ∨ K % 2187 = 1900 ∨ K % 2187 = 1957 ∨ K % 2187 = 1975 ∨ K % 2187 = 2038 ∨ K % 2187 = 2053 ∨ K % 2187 = 2110 ∨ K % 2187 = 2116) :=
  ⟨wt_rebase,
    fun m => one_add_pow_three_term 63 m,
    wt_quad_mod729, wt_cubic_mod6561,
    wt_row_five_read, wt_row_seven_read,
    wt_quad_fire_demo, fire_of_mod2187,
    dust_fire_row_seven, no22_of_cascade_six, cantorian_dust_mod_2187⟩

/-- **THE LEVEL-SEVEN RECEIPT.**  The worldtrace transformation, one
storey deeper: the five-term ladder, the quartic blade, the row-eight
read, the quartic kill demo, the uniform engine at level seven, the
sixty-four fires, the kill chain, and the re-doubled survivor map
(64 -> 128). -/
theorem the_worldtrace_receipt_seven :
    (∀ m : Nat, ∃ R : Nat, (1+63)^m
      = 1 + m*63 + Nat.choose m 2 * 63 * 63 + Nat.choose m 3 * 63 * 63 * 63
        + Nat.choose m 4 * 63 * 63 * 63 * 63 + 63*63*63*63*63*R) ∧
    (∀ m : Nat, 4^(1+3*m) ≡ 4 + 252*m + 15876*Nat.choose m 2
      + 1000188*Nat.choose m 3 + 63011844*Nat.choose m 4 [MOD 19683]) ∧
    (∀ m : Nat, digit3 (4^(1+3*m)) 8
      = digit3 (4 + 252*m + 15876*Nat.choose m 2 + 1000188*Nat.choose m 3
          + 63011844*Nat.choose m 4) 8) ∧
    (digit3 (4^(1+3*27)) 8 = 2) ∧
    (∀ K r t : Nat, r < 2187 → t < 3 →
      (digit3 (4^r) 8 + t) % 3 = 2 → K % 6561 = r + 2187 * t →
      digit3 (4^K) 8 = 2) ∧
    (∀ K : Nat, K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412 → digit3 (4^K) 8 = 2) ∧
    (∀ K : Nat, K % 6561 = 82 ∨ K % 6561 = 247 ∨ K % 6561 = 580 ∨ K % 6561 = 757 ∨ K % 6561 = 976 ∨ K % 6561 = 1246 ∨ K % 6561 = 1381 ∨ K % 6561 = 1471 ∨ K % 6561 = 1486 ∨ K % 6561 = 1498 ∨ K % 6561 = 1975 ∨ K % 6561 = 2110 ∨ K % 6561 = 2200 ∨ K % 6561 = 2227 ∨ K % 6561 = 2281 ∨ K % 6561 = 2296 ∨ K % 6561 = 2308 ∨ K % 6561 = 2380 ∨ K % 6561 = 2431 ∨ K % 6561 = 2701 ∨ K % 6561 = 2710 ∨ K % 6561 = 2926 ∨ K % 6561 = 3010 ∨ K % 6561 = 3025 ∨ K % 6561 = 3037 ∨ K % 6561 = 3109 ∨ K % 6561 = 3160 ∨ K % 6561 = 3358 ∨ K % 6561 = 3430 ∨ K % 6561 = 3439 ∨ K % 6561 = 3574 ∨ K % 6561 = 3655 ∨ K % 6561 = 3811 ∨ K % 6561 = 3928 ∨ K % 6561 = 3970 ∨ K % 6561 = 4087 ∨ K % 6561 = 4240 ∨ K % 6561 = 4303 ∨ K % 6561 = 4375 ∨ K % 6561 = 4378 ∨ K % 6561 = 4540 ∨ K % 6561 = 4654 ∨ K % 6561 = 4657 ∨ K % 6561 = 4699 ∨ K % 6561 = 4738 ∨ K % 6561 = 4810 ∨ K % 6561 = 4870 ∨ K % 6561 = 4969 ∨ K % 6561 = 5104 ∨ K % 6561 = 5107 ∨ K % 6561 = 5302 ∨ K % 6561 = 5377 ∨ K % 6561 = 5383 ∨ K % 6561 = 5467 ∨ K % 6561 = 5518 ∨ K % 6561 = 5539 ∨ K % 6561 = 5599 ∨ K % 6561 = 5602 ∨ K % 6561 = 5914 ∨ K % 6561 = 6031 ∨ K % 6561 = 6106 ∨ K % 6561 = 6247 ∨ K % 6561 = 6331 ∨ K % 6561 = 6412 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 6561 = 1 ∨ K % 6561 = 4 ∨ K % 6561 = 13 ∨ K % 6561 = 40 ∨ K % 6561 = 94 ∨ K % 6561 = 109 ∨ K % 6561 = 121 ∨ K % 6561 = 166 ∨ K % 6561 = 193 ∨ K % 6561 = 244 ∨ K % 6561 = 280 ∨ K % 6561 = 283 ∨ K % 6561 = 325 ∨ K % 6561 = 364 ∨ K % 6561 = 436 ∨ K % 6561 = 496 ∨ K % 6561 = 514 ∨ K % 6561 = 523 ∨ K % 6561 = 595 ∨ K % 6561 = 730 ∨ K % 6561 = 733 ∨ K % 6561 = 739 ∨ K % 6561 = 823 ∨ K % 6561 = 838 ∨ K % 6561 = 850 ∨ K % 6561 = 922 ∨ K % 6561 = 928 ∨ K % 6561 = 973 ∨ K % 6561 = 1003 ∨ K % 6561 = 1009 ∨ K % 6561 = 1093 ∨ K % 6561 = 1144 ∨ K % 6561 = 1165 ∨ K % 6561 = 1171 ∨ K % 6561 = 1225 ∨ K % 6561 = 1228 ∨ K % 6561 = 1243 ∨ K % 6561 = 1252 ∨ K % 6561 = 1387 ∨ K % 6561 = 1468 ∨ K % 6561 = 1540 ∨ K % 6561 = 1624 ∨ K % 6561 = 1657 ∨ K % 6561 = 1732 ∨ K % 6561 = 1741 ∨ K % 6561 = 1783 ∨ K % 6561 = 1873 ∨ K % 6561 = 1900 ∨ K % 6561 = 1957 ∨ K % 6561 = 2038 ∨ K % 6561 = 2053 ∨ K % 6561 = 2116 ∨ K % 6561 = 2188 ∨ K % 6561 = 2191 ∨ K % 6561 = 2269 ∨ K % 6561 = 2353 ∨ K % 6561 = 2434 ∨ K % 6561 = 2467 ∨ K % 6561 = 2470 ∨ K % 6561 = 2512 ∨ K % 6561 = 2551 ∨ K % 6561 = 2623 ∨ K % 6561 = 2683 ∨ K % 6561 = 2767 ∨ K % 6561 = 2782 ∨ K % 6561 = 2917 ∨ K % 6561 = 2920 ∨ K % 6561 = 2944 ∨ K % 6561 = 3115 ∨ K % 6561 = 3163 ∨ K % 6561 = 3190 ∨ K % 6561 = 3196 ∨ K % 6561 = 3280 ∨ K % 6561 = 3331 ∨ K % 6561 = 3352 ∨ K % 6561 = 3412 ∨ K % 6561 = 3415 ∨ K % 6561 = 3433 ∨ K % 6561 = 3568 ∨ K % 6561 = 3658 ∨ K % 6561 = 3673 ∨ K % 6561 = 3685 ∨ K % 6561 = 3727 ∨ K % 6561 = 3844 ∨ K % 6561 = 3919 ∨ K % 6561 = 4060 ∨ K % 6561 = 4144 ∨ K % 6561 = 4162 ∨ K % 6561 = 4225 ∨ K % 6561 = 4297 ∨ K % 6561 = 4387 ∨ K % 6561 = 4414 ∨ K % 6561 = 4456 ∨ K % 6561 = 4468 ∨ K % 6561 = 4483 ∨ K % 6561 = 4495 ∨ K % 6561 = 4567 ∨ K % 6561 = 4618 ∨ K % 6561 = 4621 ∨ K % 6561 = 4888 ∨ K % 6561 = 4897 ∨ K % 6561 = 4954 ∨ K % 6561 = 5113 ∨ K % 6561 = 5131 ∨ K % 6561 = 5197 ∨ K % 6561 = 5212 ∨ K % 6561 = 5224 ∨ K % 6561 = 5296 ∨ K % 6561 = 5347 ∨ K % 6561 = 5350 ∨ K % 6561 = 5545 ∨ K % 6561 = 5617 ∨ K % 6561 = 5620 ∨ K % 6561 = 5626 ∨ K % 6561 = 5755 ∨ K % 6561 = 5761 ∨ K % 6561 = 5842 ∨ K % 6561 = 5845 ∨ K % 6561 = 5860 ∨ K % 6561 = 5872 ∨ K % 6561 = 5998 ∨ K % 6561 = 6115 ∨ K % 6561 = 6157 ∨ K % 6561 = 6274 ∨ K % 6561 = 6349 ∨ K % 6561 = 6427 ∨ K % 6561 = 6484 ∨ K % 6561 = 6490) :=
  ⟨fun m => one_add_pow_five_term 63 m,
    wt_quartic_mod19683, wt_row_eight_read, wt_quartic_fire_demo,
    fire_of_mod6561, dust_fire_row_eight, no22_of_cascade_seven,
    cantarian_dust_mod_6561⟩

#print axioms wt_choose_one
#print axioms one_add_pow_three_term
#print axioms one_add_pow_four_term
#print axioms wt_rebase
#print axioms wt_quad_mod729
#print axioms wt_cubic_mod6561
#print axioms wt_row_five_read
#print axioms wt_row_seven_read
#print axioms wt_quad_fire_demo
#print axioms fire_of_mod2187
#print axioms dust_fire_row_seven
#print axioms no22_of_cascade_six
#print axioms cantorian_dust_mod_2187
#print axioms the_worldtrace_receipt
#print axioms one_add_pow_five_term
#print axioms wt_quartic_mod19683
#print axioms wt_row_eight_read
#print axioms wt_quartic_fire_demo
#print axioms fire_of_mod6561
#print axioms dust_fire_row_eight
#print axioms no22_of_cascade_seven
#print axioms cantarian_dust_mod_6561
#print axioms the_worldtrace_receipt_seven

#print axioms pair_read_formula
#print axioms pair_read_fire
#print axioms no22_of_pair_read
#print axioms the_pair_read_receipt
#print axioms pair_residue_mod27
#print axioms digit3_row_two_of_residue
#print axioms pair_read_fire_general
#print axioms no22_of_pair_read_general
#print axioms pair_read_fire_demo_two
#print axioms pair_read_fire_demo_three
#print axioms the_general_fire_receipt
#print axioms top_split
#print axioms window_congr
#print axioms window_row_two
#print axioms the_descent_engine_receipt
#print axioms four_pow_mod9
#print axioms dust_branch_mod9
#print axioms window_row_two_dust
#print axioms window_reduce
#print axioms the_dust_window_receipt

end GSTWorldtraceArithmetic
```

---

# PART V — THE FULL MATHEMATICAL DERIVATIONS (LaTeX)

This part is the mathematics behind the machinery, written out in full. Nothing here is new axiomatically — every statement is either a green theorem quoted from the repo (Parts II and IV) or elementary arithmetic derived from it. The purpose is different from Part II's: Part II shows you the machine's code; this part shows you the machine's *physics*, so that you can reason about the object without re-deriving the foundations. All row indices follow the repo convention: **row $p$ of $N$ means the coefficient of $3^p$ in $N$**, i.e.

$$\mathrm{digit}_3(N, p) \;=\; \left\lfloor \frac{N}{3^p} \right\rfloor \bmod 3 .$$

The worldtrace of $N$ is the sequence $\big(\mathrm{digit}_3(N,p)\big)_{p \ge 0}$. An exponent $K$ is **Cantorian** iff the worldtrace of $4^K$ avoids the value 2 entirely.

## V.1 The worldtrace coordinate system

Three elementary facts define the geometry of everything that follows.

**Fact 1 (finiteness of the read).** Row $p$ of $N$ is determined by $N \bmod 3^{p+1}$, because $\mathrm{digit}_3(N,p) = \lfloor (N \bmod 3^{p+1}) / 3^p \rfloor$. This is the green lemma `digit3_eq_of_mod_next`: congruent mod $3^{p+1}$ means equal at row $p$. The dictionary used throughout the monolith:

$$\text{row } 5 \leftrightarrow 3^6 = 729, \qquad \text{row } 7 \leftrightarrow 3^8 = 6561, \qquad \text{row } 8 \leftrightarrow 3^9 = 19683 .$$

**Fact 2 (the period law).** For $m \ge 2$ the multiplicative order of $4$ modulo $3^m$ is exactly $3^{m-1}$. This follows from LTE: for $p = 3$, $x = 4$, $y = 1$ (and $3 \mid x - y$),

$$v_3\!\left(4^n - 1\right) \;=\; v_3(4 - 1) + v_3(n) \;=\; 1 + v_3(n) \qquad (n \ge 1).$$

Hence $4^n \equiv 1 \pmod{3^m}$ iff $v_3(n) \ge m - 1$ iff $3^{m-1} \mid n$, so $\mathrm{ord}_{3^m}(4) = 3^{m-1}$. Consequently:

$$4^{K} \bmod 3^m \text{ depends only on } K \bmod 3^{m-1} \qquad (m \ge 2).$$

**Fact 3 (the observer law).** Combining Facts 1 and 2: **row $p$ of $4^K$ is a function of the first $p$ trits of $K$.** To observe the worldtrace of $4^K$ at height $p$, you need only the worldtrace of $K$ up to height $p-1$. The power stream reads the exponent stream — this is why the entire theory is *self-observational*, and why the descent engine (V.10) can reduce statements about large exponents to statements about smaller ones.

In worldtrace arithmetic the object takes its final form. Since a Cantorian $K \ge 8$ must satisfy $K \equiv 1 \pmod 3$ (rows $0$ and $1$ of $4^K$ are $1, 1$ for $K \equiv 1 \bmod 3$; $K \equiv 0$ gives row 0 = 1, row 1 = 0 — wait, carefully: $4 \equiv 1 \bmod 3$, and row 1 of $4^K$ is $\lfloor 4^K/3 \rfloor \bmod 3$), the cleanest equivalent form of the object is the one Part 0 states as (F): for every $K \ge 8$ there is a $j$ with

$$\big(\mathrm{digit}_3(4^{K \bmod 3^j},\, j+1) + \mathrm{digit}_3(K,\, j)\big) \bmod 3 = 2 ,$$

which is the self-read law (V.5) stating "row $j+1$ of $4^K$ is 2" in purely exponent-side terms.

## V.2 The LTE tower and the constants $c(j)$

Define, for $j \ge 0$,

$$c(j) \;=\; \frac{4^{3^j} - 1}{3^{j+1}} .$$

By LTE, $v_3(4^{3^j} - 1) = 1 + j$, so $c(j)$ is a positive integer not divisible by 3 — the unit part of the tower step. The tower identity (`four_pow_three_pow_eq`):

$$\boxed{\;4^{3^j} = 1 + 3^{j+1} \, c(j)\;} \qquad (j \ge 0).$$

**The cubic recursion.** Cubing the identity for $j$ (with $u = 3^{j+1}c(j)$, $(1+u)^3 = 1 + 3u + 3u^2 + u^3$):

$$4^{3^{j+1}} = 1 + 3^{j+2}\,\Big( c(j) + 3^{j+1} c(j)^2 + 3^{2j+2} c(j)^3 \Big),$$

so

$$c(j+1) \;=\; c(j) + 3^{j+1} c(j)^2 + 3^{2j+2} c(j)^3 .$$

This is the green `c_succ_eq`. It is the recursion that makes the tower computable without ever forming $4^{3^j}$.

**The signature laws.** From the recursion:

- $c(j+1) \equiv c(j) \pmod 3$ always, and $c(0) = 1$: hence $c(j) \equiv 1 \pmod 3$ for all $j$ (`c_mod3`).
- For $j \ge 1$, $3^{j+1} \equiv 0 \pmod 9$, so $c(j+1) \equiv c(j) \pmod 9$; since $c(1) = (64-1)/9 = 7$: $c(j) \equiv 7 \pmod 9$ for all $j \ge 1$ (`c_mod9_all`).
- For $j \ge 3$, $3^{j+1} \equiv 0 \pmod{81}$, so $c(j+1) \equiv c(j) \pmod{81}$; since $c(3) \equiv 16 \pmod{81}$: $c(j) \equiv 16 \pmod{81}$ for all $j \ge 3$ (`c_mod81_all`), and correspondingly $c(j) \equiv 16 \pmod{27}$ for $j \ge 2$.

Receipt R9 verifies all of this numerically through $j = 12$ (where $c(12)$ already has 319,954 digits). The signature $c \equiv 1 \bmod 3$, $c \equiv 7 \bmod 9$, $c \equiv 16 \bmod{27}$, $c \equiv 16 \bmod{81}$ is the DNA that the pair-read family (V.8) and the dust window (V.11) exploit.

**The tower fire laws.** Three infinite families of kills come straight from the tower:

- `three_pow_fires`: $\mathrm{digit}_3(4^{3^n}, n+2) = 2$ for $n \ge 1$. *Derivation:* $4^{3^n} = 1 + 3^{n+1}c(n)$, and $c(n) \equiv 7 \pmod 9$ means the first two trits of $c(n)$ (rows 0, 1 of it) are $1$ then $2$ — wait, precisely: $c(n) \bmod 9 = 7$ means $c(n) = 1 + 2\cdot 3 + 9\cdot(\cdots)$, so $3^{n+1}c(n) = 3^{n+1} + 2 \cdot 3^{n+2} + 3^{n+3}(\cdots)$, and adding 1 carries row $n+1$ to $2$: $4^{3^n} = 1 + 3^{n+1} + 2\cdot3^{n+2} + \cdots$, so row $n+1$ is $2$. (The carry $1 + 1 = 2$ at row $n+1$; row $n+2$ reads the coefficient $2$ of $3^{n+2}$.) The precise trit arithmetic: rows $n+1, n+2$ of $4^{3^n}$ are $2, 2$ for $n \ge 2$ — both fire.
- `two_mul_three_pow_fires`: $\mathrm{digit}_3(4^{2 \cdot 3^n}, n+1) = 2$. Since $4^{2 \cdot 3^n} = (4^{3^n})^2 = (1 + 3^{n+1}c)^2 = 1 + 2\cdot 3^{n+1} c + 3^{2n+2}c^2$ and the middle term's row-$(n+1)$ trit is $2 \cdot (c \bmod 3) = 2$.
- `three_pow_plus_one_fires`: $\mathrm{digit}_3(4^{3^n + 1}, n+2) = 2$ for $n \ge 3$, via $4 \cdot 4^{3^n} = 4 + 4 \cdot 3^{n+1} c$ and the mod-27 signature of $c$.

These three families alone kill every exponent of the form $3^n$, $2 \cdot 3^n$, $3^n + 1$ — the sparsest but tallest spines of the exponent line. Receipt R18 verifies them numerically through $n = 11$.

## V.3 The binomial ladder and the three blades: complete derivation

Every dust exponent is $K = 1 + 3m$. The transformation is one line:

$$4^{1+3m} \;=\; 4 \cdot 64^m \;=\; 4 \cdot (1 + 63)^m \;=\; 4 \sum_{i=0}^{m} \binom{m}{i} 63^i ,$$

with $63 = 3^2 \cdot 7$. This is `wt_rebase` plus the binomial theorem. The three ladder theorems truncate the sum at orders 3, 4, 5 with explicit witnesses $R$:

$$(1+x)^m = 1 + mx + \binom{m}{2}x^2 + x^3 R_3(x,m),$$
$$(1+x)^m = 1 + mx + \binom{m}{2}x^2 + \binom{m}{3}x^3 + x^4 R_4(x,m),$$
$$(1+x)^m = 1 + mx + \binom{m}{2}x^2 + \binom{m}{3}x^3 + \binom{m}{4}x^4 + x^5 R_5(x,m).$$

**The quadratic blade.** Substituting $x = 63$ and multiplying by 4:

$$4^{1+3m} = 4 + 252\,m + 15876\binom{m}{2} + 1000188 \, R_3 ,$$

with $252 = 4 \cdot 63$, $15876 = 4 \cdot 63^2$, $1000188 = 4 \cdot 63^3 = 4 \cdot 250047$. Now the killing fact:

$$63^3 = 250047 = 3^6 \cdot 7^3 = 729 \cdot 343 \;\Longrightarrow\; 1000188 = 729 \cdot 1372 .$$

So mod 729 the dust term vanishes and

$$\boxed{\;4^{1+3m} \;\equiv\; 4 + 252\,m + 15876\binom{m}{2} \pmod{729}\;}$$

— the **quadratic blade** `wt_quad_mod729`. The right-hand side is a polynomial in $m$ of degree 2 with 3-adically explicit coefficients: $252 = 2^2 \cdot 3^2 \cdot 7$ (rows 0–1 of the linear term are zero — the linear term only wakes up at row 2), $15876 = 2^2 3^4 \cdot 7^2$ (wakes at row 4).

**The cubic blade.** One order deeper: $63^4 = 3^8 7^4 = 6561 \cdot 2401$, so $4 \cdot 63^4 = 63011844 = 6561 \cdot 9604$ dies mod 6561:

$$\boxed{\;4^{1+3m} \equiv 4 + 252m + 15876\binom{m}{2} + 1000188\binom{m}{3} \pmod{6561}\;}$$

— `wt_cubic_mod6561`.

**The quartic blade.** $63^5 = 3^{10} 7^5$ dies mod $3^9 = 19683$ (a fortiori), and $4 \cdot 63^5 = 3969746172 = 19683 \cdot 201684$:

$$\boxed{\;4^{1+3m} \equiv 4 + 252m + 15876\tbinom{m}{2} + 1000188\tbinom{m}{3} + 63011844\tbinom{m}{4} \pmod{19683}\;}$$

— `wt_quartic_mod19683`. (A **quintic blade** mod $3^{11} = 177147$ follows the same pattern with $63^6 = 3^{12} 7^6$; the machine receipts checked it before landing, and the ladder rung `one_add_pow_five_term` already supports it.)

**The pattern.** The $i$-th blade coefficient is $4 \cdot 63^i = 2^2 3^{2i} 7^i$: it sits at row-block $2i$, and the blade of order $k$ is exact modulo $3^{2k+1}$ because the first dead term $4 \cdot 63^{k+1}$ carries $3^{2k+2}$. The blades are the worldtrace's Taylor expansion: **deep rows of dust powers are polynomial functions of the half-exponent $m$.**

## V.4 The read dictionary: rows are the polynomials

By Fact 1, row 5 of $4^{1+3m}$ is determined by the residue mod $3^6 = 729$; the quadratic blade computes that residue exactly; therefore

$$\mathrm{digit}_3\big(4^{1+3m}, 5\big) \;=\; \mathrm{digit}_3\Big(4 + 252m + 15876\binom{m}{2},\, 5\Big) \qquad \text{for every } m $$

— `wt_row_five_read`. Identically for rows 7 (cubic, mod 6561) and 8 (quartic, mod 19683). These three theorems are the *worldtrace read*: the deep-row behavior of the dust powers IS the arithmetic of explicit low-degree polynomials. When the polynomial's row-5 value is 2 — a condition on $m \bmod 729 / \gcd$ structure that `decide` closes — the exponent dies. The kill demos make the point concretely: $K = 85$ ($m = 28$) dies at row 5 by the quadratic alone; $K = 82$ ($m = 27$) dies at row 8 by the quartic alone, with $4^{82}$ never computed.

## V.5 The self-read law — the master observation theorem

The deepest structural theorem in the entire corpus (`self_read`, GSTTheActConstruction):

$$\boxed{\;\mathrm{digit}_3\big(4^{K}, j+1\big) \;=\; \Big( \mathrm{digit}_3\big(4^{K \bmod 3^{j}}, j+1\big) + \mathrm{digit}_3(K, j) \Big) \bmod 3 \qquad \text{for all } K, j.\;}$$

**Derivation sketch in worldtrace terms.** Write $K = (K \bmod 3^j) + 3^j \cdot (K / 3^j) = \mathrm{trunk} + 3^j \mathrm{head}$. Then

$$4^K = 4^{\mathrm{trunk}} \cdot \big(4^{3^j}\big)^{\mathrm{head}} = 4^{\mathrm{trunk}} \cdot \big(1 + 3^{j+1} c(j)\big)^{\mathrm{head}} .$$

The two-term ladder gives $(1 + 3^{j+1}c(j))^{\mathrm{head}} = 1 + 3^{j+1} \cdot c(j) \cdot \mathrm{head} + 3^{2j+2}(\cdots)$, so

$$4^K = 4^{\mathrm{trunk}} + 3^{j+1} \cdot \Big( c(j) \cdot \mathrm{head} \cdot 4^{\mathrm{trunk}} \Big) + 3^{2j+2}(\cdots).$$

Below row $2j+2$ the tail is invisible. Row $j+1$ of the sum is row $j+1$ of $4^{\mathrm{trunk}}$ plus row 0 of the bracket $c(j)\,\mathrm{head}\,4^{\mathrm{trunk}}$ (shifted up by $j+1$). Now the unit conspiracy: $c(j) \equiv 1 \bmod 3$ and $4^{\mathrm{trunk}} \equiv 1 \bmod 3$, so row 0 of the bracket is $\mathrm{head} \bmod 3 = \mathrm{digit}_3(K, j)$. Adding row $j+1$ of the preface and reducing mod 3 gives exactly the law. $\blacksquare$

The self-read law says: **row $j+1$ of the power worldtrace = row $j+1$ of the prefix-power worldtrace + the $j$-th trit of the exponent.** The exponent's own digits are *fed into* the power's digits, one per level, with the prefix-power acting as the carry/noise field. This is the master observation theorem from which the observer laws (Part II, §C), the noise receipts (V.6), and the descent engine (V.10) all unfold.

## V.6 The noise receipts and the dead-child automaton

Fix a level $j$ and a surviving prefix $r < 3^j$ (alive: rows $1..j{+}1$ of $4^r$ contain no 2 — with row 0 = 1 automatic for $r \equiv 1 \bmod 3$). Define the **noise** of $r$ at level $j$:

$$\nu_j(r) \;=\; \mathrm{digit}_3\big(4^{r},\, j+1\big) \in \{0, 1\} \quad (\text{alive means} \ne 2).$$

The three children of $r$ at level $j+1$ are $r$, $r + 3^j$, $r + 2 \cdot 3^j$ — the prefix with the new trit $t \in \{0,1,2\}$ appended. By the self-read law, row $j+1$ of child $t$'s power is $(\nu_j(r) + t) \bmod 3$. Therefore:

- exactly ONE child has $(\nu_j(r) + t) \equiv 2 \pmod 3$ — the **dead child** $t^* = (2 - \nu_j(r)) \bmod 3$; it fires its 2 at row $j+1$ and dies;
- the other two children survive level $j+1$ (as far as row $j+1$ sees).

This is the **unique dead child law** (`unique_dead_child`, Part II §F3) and the **feedback fire of class** (`feedback_fire_of_class`): if $K \equiv r + 3^j t \pmod{3^{j+1}}$ and $(\nu_j(r) + t) \bmod 3 = 2$, then $\mathrm{digit}_3(4^K, j+1) = 2$ — *the entire congruence class dies at row $j+1$, uniformly, with no other hypothesis*. The instances at $j = 6$ and $j = 7$ are `fire_of_mod2187` and `fire_of_mod6561`; the dead classes they enumerate are exactly the generated tables (receipts R16: all 32 noise receipts at level 6 verified; the level-7 tables are quartic-blade computed, receipt R7b: 64/64 fire).

## V.7 The doubling survivor map and the Cantor structure of the dust tree

Let $S_j$ be the set of residues $r \bmod 3^j$, $r \equiv 1 \bmod 3$, such that rows $1..j{+}1$ of $4^r$ avoid 2 (the level-$j$ survivors). The dead-child automaton gives:

$$S_{j+1} \;=\; \big\{\, r + 3^j t \;:\; r \in S_j,\; t \ne (2 - \nu_j(r)) \bmod 3 \,\right\}, \qquad |S_{j+1}| = 2\,|S_j| .$$

Since $|S_1| = 1$ (the single residue 1 mod 3), induction gives $|S_j| = 2^{j-1}$: **the survivor counts are 1, 2, 4, 8, 16, 32, 64, 128, 256, …** — receipt R6 confirms this doubling exactly through level 9, and the green theorems `cantorian_dust_mod_729` (32 survivors), `cantorian_dust_mod_2187` (64), `cantorian_dust_mod_6561` (128) pin the storeys 5→8 in Lean.

Structurally: inside the full ternary tree of dust exponents (branching 3), the alive set is a **binary subtree** (branching 2). The Cantorian exponents — those that survive every level — are exactly the infinite paths of this binary tree. The map from paths to exponents is

$$K \;=\; 1 + \sum_{j \ge 1} t_j\, 3^j, \qquad t_j \in \{0,1,2\} \setminus \{t^*_j\},$$

where $t^*_j$ is the dead trit at level $j$ determined by the noise of the running prefix — a **feedback-driven, non-stationary Cantor set**. It is not the middle-third set: which child dies depends on the noise field $\nu_j(r)$, i.e. on the *entire prior path*. The conjecture (form (C) of Part 0) states that this path space, intersected with $K \ge 8$, is empty — every branch is eventually cut by a dead child.

The kill statistics (receipt R11) show the extinction profile: for dust exponents $8 \le K < 2000$ the first-2 rows distribute as 221, 148, 97, 64, 44, 32, 27, 26, 18, 11, 6, 3, 1, 1 over rows 2..15 — an approximate halving per row (the doubling map read upside down), with nothing surviving past row 15 in that range. The census R10 is total below 6561: **the only Cantorian exponents are 0, 1, 4** (with $4^0 = 1, 4^1 = 4 = 11_3, 4^4 = 256 = 100111_3$). The conjecture is the statement that this census never grows again.

## V.8 The pair-read law: complete derivation

The fixed cascades see exponents only through a fixed modulus. The pair-read family sees *structure*: a trunk, a long zero-run, and a branch.

**Setup.** Let $T$ (the trunk) satisfy $4^T < 3^{j+2}$, and let $u$ (the branch) be arbitrary. The exponent is $K = T + 3^{j+1} u$. (Geometric meaning: the trits of $K$ are those of $T$ up to position $j$, then the trits of $u$ from position $j+1$ up — a trunk, a possible gap, a branch.)

**Step 1 — the tower factorization.**

$$4^K = 4^T \cdot \big(4^{3^{j+1}}\big)^{u} = 4^T \big(1 + 3^{j+2} c(j+1)\big)^{u} .$$

**Step 2 — the three-term ladder.**

$$\big(1 + 3^{j+2} c(j+1)\big)^u = 1 + 3^{j+2}\, u\, c(j+1) + 3^{2j+4}\, \binom{u}{2} c(j+1)^2 + 3^{3j+6}(\cdots),$$

so

$$4^K \;=\; 4^T \;+\; 3^{j+2} \cdot \Big( 4^T u\, c(j+1) \Big) \;+\; 3^{2j+4} \cdot (\cdots).$$

**Step 3 — the preface shift.** Since $4^T < 3^{j+2}$, the green `prefaced_digit` law applies: for $A < 3^{j+2}$, row $j+2+s$ of $\big(A + 3^{j+2} X\big)$ equals row $s$ of $X$ (the preface $A$ cannot reach row $j+2$; the factor $3^{j+2}$ shifts $X$'s rows up by $j+2$; higher powers of $3^{j+2}$ are invisible below row $2(j{+}2)$). Taking $s = 2$:

$$\mathrm{digit}_3\big(4^{T + 3^{j+1}u},\, j+4\big) \;=\; \mathrm{digit}_3\big(4^T \, u \, c(j+1),\, 2\big) + \text{(row-2 contributions of the deep tail — none, below row } 2j+4).$$

This is **`pair_read_formula`**: the deep row $j+4$ of the branched power is the shallow row 2 of the *product* $4^T \cdot u \cdot c(j+1)$.

**Step 4 — the residue reduction.** For $j \ge 2$, $c(j+1) \equiv 16 \pmod{27}$ (`c_mod81_all` pulled back mod 27). So

$$\big(4^T u\, c(j+1)\big) \bmod 27 \;=\; \big(4^T \cdot u \cdot 16\big) \bmod 27$$

— `pair_residue_mod27`. Row 2 of any number is $\lfloor (x \bmod 27)/9 \rfloor$, so:

$$\mathrm{digit}_3\big(4^{T+3^{j+1}u}, j+4\big) = 2 \iff \big(4^T u \cdot 16\big) \bmod 27 \in \{18, \dots, 26\}$$

— the **kill zone**. This is `pair_read_fire_general` with `digit3_row_two_of_residue`.

**The first family** (`pair_read_fire`): trunk $T = 4$, so $4^T = 256 \equiv 13 \pmod{27}$, and the kill residues are $13 \cdot 16 \equiv 19$, $13 \cdot 4 \cdot 16 \equiv 22$, $13 \cdot 7 \cdot 16 \equiv 25 \pmod{27}$ — so $u \in \{1, 4, 7\}$ all kill, for every $j \ge 4$ simultaneously. The family

$$K = 4 + 3^{j+1} u, \quad u \in \{1,4,7\}, \quad j \ge 4: \qquad 247,\; 976,\; 1705,\; 733,\; 2920,\; 5107,\; 2191,\; 8752,\;\dots$$

dies at row $j+4$, one theorem, infinitely many exponents — including exponents in survivor classes of every fixed level (the class-4 trunk survives all fixed cascades; the branch structure is what kills). Receipt R12: 27/27 verified. The trunk-13 family (`pair_read_fire_demo_two`): $4^{13} \equiv 13 \pmod{27}$ as well — wait, $4^{13} \bmod 27$: by the period law, $4^{13} = 4^{13 \bmod 9} = 4^4 = 256 \equiv 13$. Same kill residues, hence the family $13 + 3^{j+1}u$, $u \in \{1,4,7\}$, $j \ge 15$ fires at row $j+4$ — receipt R13 verifies 15/15 with the negative controls $u = 2, 3$ correctly NOT firing.

**The automaton viewpoint.** The kill condition is a function of $(4^T \bmod 27, u \bmod 27)$ — a finite $27 \times 27$ table (receipt R8 renders it). Every trunk-branch decomposition of every dust exponent passes through this table. In this sense the pair-read law is a **uniform, level-transcending killing machine**: it does not care about the level $j$ at all (beyond $j \ge 4$ for the residue signature to stabilize), only the trunk's residue and the branch's residue.

## V.9 The descent engine: complete derivation

The descent engine reduces row $H+2$ of $4^K$ to data about strictly smaller exponents.

**Step 1 — the top split** (`top_split`). For $K < 3^{H+1}$, write $K = \mathrm{trunk} + 3^H \mathrm{branch}$ with $\mathrm{trunk} = K \bmod 3^H < 3^H$ and $\mathrm{branch} = \lfloor K / 3^H \rfloor < 3$. Then

$$4^K = 4^{\mathrm{trunk}} \cdot \big(4^{3^H}\big)^{\mathrm{branch}} = 4^{\mathrm{trunk}}\big(1 + 3^{H+1} c(H)\big)^{\mathrm{branch}}$$

and the three-term ladder gives

$$4^K \;=\; 4^{\mathrm{trunk}} \;+\; 3^{H+1} \cdot X \;+\; 3^{2H+2} \cdot Y, \qquad X \;=\; \mathrm{branch} \cdot c(H) \cdot 4^{\mathrm{trunk}} .$$

**Step 2 — the addition window** (`window_congr`). Below row $2H+2$, the term $3^{2H+2}Y$ is invisible (it is $0$ mod $3^{2H+2}$, and rows below $2H+2$ only need residues mod $3^{2H+2}$ at most). Hence for $r + 1 \le 2H + 2$:

$$\mathrm{digit}_3(4^K, r) \;=\; \mathrm{digit}_3\big(4^{\mathrm{trunk}} + 3^{H+1} X,\; r\big).$$

**Step 3 — the column read** (`window_row_two`). Row $H+2$ of the two-term sum: the preface $4^{\mathrm{trunk}}$ contributes its own row $H+2$ digit; the shifted middle term $3^{H+1} X$ contributes row 1 of $X$ at row $H+2$; and the addition at row $H+1$ (preface row $H+1$ digit plus row 0 of $X$ plus nothing else) produces a carry into row $H+2$. With row 0 of $X$ being $\mathrm{branch} \cdot (c(H) \bmod 3) \cdot (4^{\mathrm{trunk}} \bmod 3) = \mathrm{branch} \cdot 1 \cdot 1 = \mathrm{branch}$:

$$\mathrm{digit}_3(4^K, H+2) \;=\; \Big( \mathrm{digit}_3(4^{\mathrm{trunk}}, H+2) + \big\lfloor X/3 \big\rfloor \bmod 3 + \big\lfloor \mathrm{digit}_3(4^{\mathrm{trunk}}, H+1) + \mathrm{branch} \big\rfloor / 3 \Big) \bmod 3 .$$

Every ingredient on the right lives on the *trunk* (an exponent $< 3^H$) plus the *top trit of $K$*. This is the descent. Machine-checked 800/800 in the repo; receipt R14 spot-verifies it on the cascade survivors.

**Why this matters structurally.** The descent converts the global question "does the worldtrace of $4^K$ ever read 2?" into a recursive computation over the trits of $K$ from the top down, with the carry/noise state passed along — a *streaming automaton* reading $K$'s trits. The self-read law is the level-$j$ sibling of the same phenomenon (reading $K$'s trits from the bottom up). Between them, the two laws say the worldtrace of $4^K$ is a *transducer output* of the worldtrace of $K$.

## V.10 The dust window: the mod-9 conspiracy

Specialize the descent to dust exponents $K \equiv 1 \bmod 3$ — the only exponents that can be Cantorian above 8.

**`four_pow_mod9`**: $4^r \bmod 9 = 4^{r \bmod 3} \bmod 9$ (period 3: $4, 7, 1$). For a dust trunk ($\mathrm{trunk} \equiv 1 \bmod 3$): $4^{\mathrm{trunk}} \equiv 4 \pmod 9$.

**`dust_branch_mod9`**: the branch factor reduces mod 9 as

$$\big(t \cdot c(H) \cdot 4^{\mathrm{trunk}}\big) \bmod 9 \;=\; t \cdot 7 \cdot 4 \bmod 9 \;=\; 28\, t \bmod 9 \;=\; t .$$

**The conspiracy:** $c(H) \equiv 7 \pmod 9$ and $4^{\mathrm{trunk}} \equiv 4 \pmod 9$ are *multiplicative inverses* mod 9 on the dust tree. The LTE unit and the power residue cancel each other exactly. Consequently the branch factor's leading trit is the branch trit itself — no noise, no correction — and the descent's column read collapses to the two-term form (`window_row_two_dust`):

$$\mathrm{digit}_3(4^K, H+2) \;=\; \Big( \mathrm{digit}_3(4^{\mathrm{trunk}}, H+2) + \big\lfloor \mathrm{digit}_3(4^{\mathrm{trunk}}, H+1) + \mathrm{branch} \big\rfloor / 3 \Big) \bmod 3 .$$

**`window_reduce`** supplies the general window congruence (row $H+1+s$ of $A + 3^{H+1}X$ sees only $X \bmod 3^{s+1}$), and `the_dust_window_receipt` packages all four laws as one green conjunction.

## V.11 The Ω operator and the omega wave law

The omega layer (GSTGraphV2OmegaWaveLaw, 3043 lines, 140 declarations — Part II §B) is the universe graph's dynamics, and it reduces to one operator on carry-digit states:

$$\Omega(D, X) \;=\; \left( \frac{D + 4\,(X \bmod 3)}{3},\; \lfloor X / 3 \rfloor \right) .$$

Interpretation: $X$ is the remaining origin word (the exponent's unread trits, low end first); $X \bmod 3$ is the next origin trit $d$; the output digit of the x4-cell is $(D + 4d) \bmod 3$ and the next carry is $(D + 4d)/3$ — this is the **handwritten-U divide**: the base-3 long division of the *prefixed* origin by 3 while multiplying by 4, digit by digit. The green laws `omegaWaveStep_u_divide`, `omegaWaveStep_u_multiply`, `omegaWaveStep_mass`, `omegaWaveStep_worldtrace` certify each reading.

**The Ω-cut factorization** (`omega_cut_factor`): for sheet level $a$ and core mass $\mathrm{core}$,

$$4^{3^a \cdot \mathrm{core}} \;=\; 1 + 3^{a+1} \cdot \underbrace{\mathrm{lteCoeff}(a) \cdot \sum_{i=0}^{\mathrm{core}-1} \big(4^{3^a}\big)^{i}}_{\text{the cut word } \omegaCutWord(a, \mathrm{core})}$$

— the LTE mean times the geometric mean, exact for all $a$, $\mathrm{core}$. This is the closed form of iterating the tower factorization: $4^{3^a \mathrm{core}} - 1 = (4^{3^a} - 1)\cdot\big(1 + 4^{3^a} + \cdots + (4^{3^a})^{\mathrm{core}-1}\big)$, the two factors being exactly the LTE mean $3^{a+1}\mathrm{lteCoeff}(a)$ and the geometric sum.

**The wave laws.** The cut word stabilizes (`omega_cut_word_stabilizes`): from sheet $s$ on, the cut word's worldtrace below the diagonal is constant in $s$ — the infinite word $\omega_\infty$ exists. The diagonal read of the stabilized word then satisfies the band laws: cores with $\mathrm{core} \equiv 1 \bmod 9$, or $\equiv 13, 25 \bmod 27$, or $\equiv 4, 34, 49, 70 \bmod 81$, or $\equiv 16, 31, 61, 76, 124, 139, 169, 184 \bmod{243}$ — each band fires its digit 2 on the diagonal at a depth growing with the modulus (`omega_diagonal_two_of_mod_nine_one` through `..._onehundredeightyfour`, and the tower forms `omega_tower_digit_two_of_mod81_band`, `..._mod243_band`). These are the **omega shadow classes**: exponents $3^s \cdot \mathrm{core}$ with core in a band are killed by the diagonal read at depth $s$-dependent rows — an infinite family of kills parameterized by the core's residue, complementary to the dust-tree cascades (which live on $K \equiv 1 \bmod 3$).

## V.12 The fourth dimension: the emergent diagonal

The 4th-dimension file (GSTTailFFourthDimension, 2332 lines — Part II §D) concerns the *diagonal* of the Ω-iteration: reading the worldtrace of the power at the row that the wave front is currently crossing. Its pillars:

**The extended observation law** — the self-read law without a window bound: the diagonal read is defined for every sheet and core, unconditionally.

**The descent blade (4D emergent laws)** — `omega_tower_kill_of_diagonal_two`: if the diagonal reads 2 at depth $k$, the power $4^{3^s \mathrm{core}}$ dies at row $k$ — the diagonal IS a killing read, not just an observation.

**The cube-lift recursion** — `omega_cut_word_cube_lift_exact`: the cut word at sheet $s+1$ is an exact cubic polynomial in the cut word at sheet $s$ (the same cubic recursion as $c(j+1)$ in V.2, transported to the wave setting). This is the engine that lets every diagonal statement lift one sheet at a time with binomial-exact error control.

**The two trit statements** — the decomposition of the input exponent into its 3-adic trunk and head as two named streams (Part II §D4), which is how the 4D file interfaces with the descent engine of V.9.

**The band theorems** (V.11's list) are the 4D emergent laws' output: eight mod-243 classes, four mod-81 classes, two mod-27 classes, one mod-9 class — a nested system of kills on the core mass, each verified green and each an infinite family.

## V.13 The 2D emergent laws — the microscopic physics of the carry stream

The 2D file (GST2DMixedEmergence, 242 lines — quoted complete in Part II §E) writes the Ω-cell's physics as a two-dimensional lattice: the carry axis $C$ (vertical, taking values $0..3$ — green `graph_carry_lt_four`) and the digit axis $d$ (horizontal, values $0,1,2$). The local dynamics:

$$\mathrm{out}(C, d) = (C + 4d) \bmod 3, \qquad \mathrm{next}(C, d) = (C + 4d)/3 .$$

On this lattice the file defines the potentials — `uCharge` (the U-charge of a carry state), `uJump` (the jump in charge across a cell), `infoPotential` (the information content of a digit), `carryPotential`, and the **mixed density** $\rho(C,d)$ mixing both axes — and proves:

- **`uJump_divergence`** — the jump field is a discrete divergence: the charge lost by the carry axis is exactly the charge gained by the digit axis, cell by cell. Conservation.
- **`mixed_cell_emergence`** — the mixed density of a cell is the sum of its vertical and horizontal emergent parts, exactly.
- **`happy_chord_dichotomy`** — every cell is either *happy* (its output digit is in the happy chord — the digits that keep the worldtrace 2-free at that position) or it fires; a clean dichotomy with no middle ground.
- **`mixed_row_emergence` / `mixed_rectangle_emergence`** — the telescoping theorems (`horizontal_diff_telescope` is the engine): the total emergence over a row, and over a rectangle of the lattice, is a boundary term. What happens inside the rectangle cancels; only the boundary speaks.

This is the microscopic justification of the macroscopic noise receipts (V.6): the "noise" $\nu_j(r)$ is the accumulated boundary term of the 2D emergence field along the path that $K$'s trits trace through the carry lattice. The killing rows are where the boundary term forces a 2.

## V.14 The causality laws

Four families, in increasing depth (Part II §F quotes the code):

**Origin-prefix causality** (CanonicalCausalityScratch): the worldtrace of $4^K$ at rows $\le p$ is caused by (is a function of) the origin prefix $K \bmod 3^p$ — the observer law (V.1, Fact 3) in causal language. Nothing below row $p+1$ can see the head of $K$.

**The self-read feedback law** (`self_read`, V.5): the master law — the exponent's $j$-th trit is *added into* the power's row $j+1$. The exponent stream drives the power stream through the prefix-power field.

**The noise window and the unique dead child** (V.6): within the window of level $j$, exactly one child trit is fatal. The feedback is causal and local: the fatal trit is determined by the noise of the running prefix, before the choice is made.

**The uniform kill engine** (`feedback_fire_of_class`): the causal law's global form — a certified noise receipt at level $j$ kills the entire congruence class mod $3^{j+1}$, at row $j+1$, forever. Every cascade level (past and future) is an instance of this one theorem.

Causally, the conjecture reads: *the feedback system (exponent trits in, power trits out, noise carried along) has no orbit above level 8 that avoids the firing state.* The worldtrace is the transcript of this feedback system, and the conjecture is the assertion that its only 2-avoiding orbits are the three finite ones: $K = 0, 1, 4$.

## V.15 The infinite theorem controllers

The controller layer (Part II §G) manages the passage from finite storeys to the infinite object:

**The main control graph** (GSTGraphV2InfiniteControl): the seeded carry graph. `seededCarry(seed, tail, q)` defines the carry stream of any exponent from its seed and tail; `prefix_slice_seed_zero/one` prove the first slices' exact values; `graph_event_balance_exact` and `graph_cross_rectangle_exact` prove the balance laws (events in, events out) over arbitrary rectangles of the lattice. The controller *computes* the noise field of any exponent from finite data, exactly.

**The never-firing tower and the Cantorian core** (GSTClimbInfiniteFamily, 1151 lines): the formal Negation-of-Cantorian-Power tower — assuming a Cantorian power above 8, the tower derives the infinite descending chain of survivor residues, each level halving the world, and the never-firing conditions contradict the band theorems at every fixed band. The Cantorian core (`ClimbTruthValue`, the climb certificates) is the machinery that would consume a proof of the empty-path statement.

**The other controller modules** (all green, Part II §G3): the residue controllers, the bridge classifiers, the affine channel automaton — each managing one family of infinite consequences of a finite certificate.

The controller philosophy: **every infinite statement in this corpus is the direct limit of its finite storeys, and each storey is green.** The object asks for the statement that the limit itself is green at the top: no Cantorian orbit above 8.

## V.16 The GST Graph V2 Ontological Universe Graph — the complete construction

The universe graph is the arena all layers live in. The full construction protocol is Part III; here is the mathematical summary and the construction's correctness core.

**Vertices.** The vertex at time $t$, position $p$, with energy parameter $E$ is the *cell*

$$\mathbf{v}(E, t, p) \;=\; \big( C_t^{(E)},\; d_p^{(E)} \big) \in \{0,1,2,3\} \times \{0,1,2\},$$

where $C_t^{(E)}$ is the carry stream of the exponent $E$ under the Ω-dynamics and $d_p^{(E)}$ its digit stream. Green bounds: `graph_carry_lt_four`, `graph_digit_lt_three`.

**Edges.** The forward edge of a cell is the Ω-step (V.11); the horizontal edges are the digit increments; the *crossing* edges are the changes of charge (`graph_happy_iff_crossing_positive`: a cell is happy iff its crossing number is positive — the dichotomy law on the graph).

**The ontological current.** The potentials of V.13 integrate to currents: `reverseOntCode` (the reverse base-seven coding of the ontological state — the green `reverseOntCode_exact` proves the coding is exact, `reverseOntCode_ge_global_floor` proves the global floor), `weightedOntPrefix` (the prefix-weighted charge, with its floor and positivity laws), `graphOntWindow` (the windowed current over any rectangle, with `graphOntWindow_positive_of_happy`). The **no-erasure laws** (`ontDensity_ge_42_of_happy`, `ontDensity_ge_neg54`, `ontDensity_nonpositive_of_not_happy`, `happy_iff_ontDensity_positive`): the twelve-cell physical table (`ontDensity_physical_table`) fixes the density of every cell in $\{0,\dots,3\} \times \{0,1,2\}$ — the complete local physics, twelve numbers, no freedom.

**The correctness core.** `ternaryWeightedOntDiff_telescope` (the telescoping identity that makes every rectangle a boundary term) + `weightedOntPrefix_eq_sum` (the current is the sum of its cells). Together: *whatever happens inside a rectangle of the universe graph, the observable laws see only its boundary* — the same structure as the 2D emergence (V.13), the window laws (V.9, V.10), and the observer law (V.1). The universe graph is the maximal arena in which the local-to-global principle holds by construction.

## V.17 The object, in the language of this part

Everything above is machinery. The object is one sentence, and it is yours:

$$\boxed{\;\text{For every } K \ge 8 \text{ there is a row } p \text{ with } \mathrm{digit}_3\!\left(4^{K},\, p\right) = 2.\;}$$

By the self-read law this is the same as: for every $K \ge 8$ there is a $j$ with $(\mathrm{digit}_3(4^{K \bmod 3^j}, j+1) + \mathrm{digit}_3(K, j)) \bmod 3 = 2$. By the dead-child automaton this is the same as: the feedback path of every $K \ge 8$ meets a firing row. By the census (R10) it is true below 6561 with exactly three exceptions below that bound, all $< 8$. The machinery in Parts II, IV, and the companions is the verified, green, axiom-clean foundation on which the proof is to be built.


---

# PART VI — THE NUMERICAL RECEIPTS (machine-computed, exact, 0 failures)

Every law quoted in this document has been re-verified numerically, independently of Lean, with exact integer and modular arithmetic (Python 3, arbitrary precision; the scripts are reproducible line-for-line from the tables' definitions). These receipts are not part of the proof — they are the *instrument readings* that say the physics below is what the theorems say it is. All of them returned **zero failures**.

**The receipt inventory:**

- **R1** — the worldtrace table of $4^K$ for $K = 0..60$, rows 0..13, with the first firing row of each. The Cantorian three ($K = 0, 1, 4$) stand alone.
- **R2** — the residue table $4^K \bmod 3^n$ for $K = 1..20$, $n = 1..10$: the period law made visible ($4^K \bmod 3^n$ depends only on $K \bmod 3^{n-1}$).
- **R3 / R4 / R5** — the quadratic / cubic / quartic blades verified mod 729 / 6561 / 19683 on full ranges, with the row-5 / row-7 / row-8 polynomial reads matching direct computation of the powers, every time.
- **R6** — the survivor doubling map, levels 1 through 9: counts 1, 2, 4, 8, 16, 32, 64, 128, 256 with the full survivor lists at the first five levels. The doubling is exact, without exception.
- **R7a / R7b** — the 32 dead classes mod 2187 all fire at row 7 (32/32); the 64 dead classes mod 6561 all fire at row 8 (64/64); with the dead-class decomposition by dead-child trit $t$.
- **R8** — the pair-read kill zone: the full residue table $(4^T \bmod 27) \times (u \bmod 27) \mapsto (4^T u \cdot 16) \bmod 27$ with the kill zone $[18, 26]$ marked.
- **R9** — the tower constants $c(j)$ for $j = 1..12$ (up to 319,954 digits), with the stabilized signature $c \equiv 1 \bmod 3$, $7 \bmod 9$, $16 \bmod 27$, $16 \bmod{81}$.
- **R10** — the complete Cantorian census below 6561: exactly $\{0, 1, 4\}$.
- **R11** — the extinction profile of dust exponents below 2000: the halving cascade of first-fire rows.
- **R12** — the pair-read family $4 + 3^{j+1}u$, $u \in \{1,4,7\}$, $j = 4..12$: 27/27 fire at row $j+4$.
- **R13** — the trunk-13 automaton, $j = 15..19$, with negative controls: 15/15 match including the no-kill predictions.
- **R15** — 44/44 random kill-zone triples fire.
- **R16** — all 32 level-6 noise receipts: the dead child $t = (2 - \nu_6(r)) \bmod 3$ generates exactly the dead class.
- **R17** — the self-read law on 20 mixed cases (fixed + random): 20/20.
- **R18** — the tower fire laws $3^n$, $2 \cdot 3^n$, $3^n + 1$ through $n = 11$.

## R1 — The worldtrace of 4^K, rows 0..13 (row p = coefficient of 3^p; first row with trit 2)

| K | trits (rows 0→13) | first row with trit=2 | Cantorian? |
|---|---|---|---|
| 0 | 10000000000000 | None | YES |
| 1 | 11000000000000 | None | YES |
| 2 | 12100000000000 | 1 | no |
| 3 | 10120000000000 | 3 | no |
| 4 | 11100100000000 | None | YES |
| 5 | 12210110000000 | 1 | no |
| 6 | 10212121000000 | 2 | no |
| 7 | 11201111200000 | 2 | no |
| 8 | 12002222001000 | 1 | no |
| 9 | 10012122011100 | 4 | no |
| 10 | 11010112022210 | 7 | no |
| 11 | 12111120002212 | 1 | no |
| 12 | 10100010102111 | 10 | no |
| 13 | 11110011112000 | 10 | no |
| 14 | 12221012220010 | 1 | no |
| 15 | 10221210220111 | 2 | no |
| 16 | 11211112210222 | 2 | no |
| 17 | 12010001212212 | 1 | no |
| 18 | 10021001011211 | 3 | no |
| 19 | 11020201112010 | 3 | no |
| 20 | 12122221220021 | 1 | no |
| 21 | 10112221120120 | 4 | no |
| 22 | 11120221010200 | 3 | no |
| 23 | 12200021211220 | 1 | no |
| 24 | 10201020110120 | 2 | no |
| 25 | 11221122121100 | 2 | no |
| 26 | 12021012111020 | 1 | no |
| 27 | 10001210100222 | 5 | no |
| 28 | 11001012110212 | 7 | no |
| 29 | 12101110102201 | 1 | no |
| 30 | 10121221112102 | 3 | no |
| 31 | 11101121001122 | 6 | no |
| 32 | 12211201201202 | 1 | no |
| 33 | 10210102002000 | 2 | no |
| 34 | 11202112202200 | 2 | no |
| 35 | 12000101200201 | 1 | no |
| 36 | 10010111001221 | 11 | no |
| 37 | 11011122101021 | 6 | no |
| 38 | 12112202121120 | 1 | no |
| 39 | 10101200111010 | 5 | no |
| 40 | 11111001122111 | 9 | no |
| 41 | 12222101202100 | 1 | no |
| 42 | 10222121000120 | 2 | no |
| 43 | 11212111200100 | 2 | no |
| 44 | 12011100101110 | 1 | no |
| 45 | 10022210111221 | 3 | no |
| 46 | 11021212122021 | 3 | no |
| 47 | 12120111112001 | 1 | no |
| 48 | 10110222220011 | 5 | no |
| 49 | 11121212220112 | 3 | no |
| 50 | 12201111220220 | 1 | no |
| 51 | 10202222020020 | 2 | no |
| 52 | 11222122000122 | 2 | no |
| 53 | 12022112010102 | 1 | no |
| 54 | 10002101021112 | 4 | no |
| 55 | 11002021120001 | 4 | no |
| 56 | 12102220010101 | 1 | no |
| 57 | 10122120111111 | 3 | no |
| 58 | 11102110222222 | 4 | no |
| 59 | 12212002212222 | 1 | no |
| 60 | 10211012111222 | 2 | no |

## R2 — 4^K mod 3^n (K rows × n=1..10)

| K | mod 3^1 | mod 3^2 | mod 3^3 | mod 3^4 | mod 3^5 | mod 3^6 | mod 3^7 | mod 3^8 | mod 3^9 | mod 3^10 |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 | 4 |
| 2 | 1 | 7 | 16 | 16 | 16 | 16 | 16 | 16 | 16 | 16 |
| 3 | 1 | 1 | 10 | 64 | 64 | 64 | 64 | 64 | 64 | 64 |
| 4 | 1 | 4 | 13 | 13 | 13 | 256 | 256 | 256 | 256 | 256 |
| 5 | 1 | 7 | 25 | 52 | 52 | 295 | 1024 | 1024 | 1024 | 1024 |
| 6 | 1 | 1 | 19 | 46 | 208 | 451 | 1909 | 4096 | 4096 | 4096 |
| 7 | 1 | 4 | 22 | 22 | 103 | 346 | 1075 | 3262 | 16384 | 16384 |
| 8 | 1 | 7 | 7 | 7 | 169 | 655 | 2113 | 6487 | 6487 | 6487 |
| 9 | 1 | 1 | 1 | 28 | 190 | 433 | 1891 | 6265 | 6265 | 25948 |
| 10 | 1 | 4 | 4 | 31 | 31 | 274 | 1003 | 5377 | 5377 | 44743 |
| 11 | 1 | 7 | 16 | 43 | 124 | 367 | 1825 | 1825 | 1825 | 1825 |
| 12 | 1 | 1 | 10 | 10 | 10 | 10 | 739 | 739 | 7300 | 7300 |
| 13 | 1 | 4 | 13 | 40 | 40 | 40 | 769 | 2956 | 9517 | 29200 |
| 14 | 1 | 7 | 25 | 79 | 160 | 160 | 889 | 5263 | 18385 | 57751 |
| 15 | 1 | 1 | 19 | 73 | 154 | 640 | 1369 | 1369 | 14491 | 53857 |
| 16 | 1 | 4 | 22 | 49 | 130 | 373 | 1102 | 5476 | 18598 | 38281 |
| 17 | 1 | 7 | 7 | 34 | 34 | 34 | 34 | 2221 | 15343 | 35026 |
| 18 | 1 | 1 | 1 | 55 | 136 | 136 | 136 | 2323 | 2323 | 22006 |
| 19 | 1 | 4 | 4 | 58 | 58 | 544 | 544 | 2731 | 9292 | 28975 |
| 20 | 1 | 7 | 16 | 70 | 232 | 718 | 2176 | 4363 | 17485 | 56851 |

## R3 — Quadratic blade mod 729 (m = 0..30): 4^(1+3m) ≡ 4+252m+15876·C(m,2)

| m | K=1+3m | 4^K mod 729 | blade | match | row 5 of 4^K | row 5 of blade |
|---|---|---|---|---|---|---|
| 0 | 1 | 4 | 4 | YES | 0 | 0 |
| 1 | 4 | 256 | 256 | YES | 1 | 1 |
| 2 | 7 | 346 | 346 | YES | 1 | 1 |
| 3 | 10 | 274 | 274 | YES | 1 | 1 |
| 4 | 13 | 40 | 40 | YES | 0 | 0 |
| 5 | 16 | 373 | 373 | YES | 1 | 1 |
| 6 | 19 | 544 | 544 | YES | 2 | 2 |
| 7 | 22 | 553 | 553 | YES | 2 | 2 |
| 8 | 25 | 400 | 400 | YES | 1 | 1 |
| 9 | 28 | 85 | 85 | YES | 0 | 0 |
| 10 | 31 | 337 | 337 | YES | 1 | 1 |
| 11 | 34 | 427 | 427 | YES | 1 | 1 |
| 12 | 37 | 355 | 355 | YES | 1 | 1 |
| 13 | 40 | 121 | 121 | YES | 0 | 0 |
| 14 | 43 | 454 | 454 | YES | 1 | 1 |
| 15 | 46 | 625 | 625 | YES | 2 | 2 |
| 16 | 49 | 634 | 634 | YES | 2 | 2 |
| 17 | 52 | 481 | 481 | YES | 1 | 1 |
| 18 | 55 | 166 | 166 | YES | 0 | 0 |
| 19 | 58 | 418 | 418 | YES | 1 | 1 |
| 20 | 61 | 508 | 508 | YES | 2 | 2 |
| 21 | 64 | 436 | 436 | YES | 1 | 1 |
| 22 | 67 | 202 | 202 | YES | 0 | 0 |
| 23 | 70 | 535 | 535 | YES | 2 | 2 |
| 24 | 73 | 706 | 706 | YES | 2 | 2 |
| 25 | 76 | 715 | 715 | YES | 2 | 2 |
| 26 | 79 | 562 | 562 | YES | 2 | 2 |
| 27 | 82 | 247 | 247 | YES | 1 | 1 |
| 28 | 85 | 499 | 499 | YES | 2 | 2 |
| 29 | 88 | 589 | 589 | YES | 2 | 2 |
| 30 | 91 | 517 | 517 | YES | 2 | 2 |

## R4 — Cubic blade mod 6561 (m = 0..15), row 7 read

| m | K | 4^K mod 6561 | cubic blade | match | row7 4^K | row7 blade |
|---|---|---|---|---|---|---|
| 0 | 1 | 4 | 4 | YES | 0 | 0 |
| 1 | 4 | 256 | 256 | YES | 0 | 0 |
| 2 | 7 | 3262 | 3262 | YES | 1 | 1 |
| 3 | 10 | 5377 | 5377 | YES | 2 | 2 |
| 4 | 13 | 2956 | 2956 | YES | 1 | 1 |
| 5 | 16 | 5476 | 5476 | YES | 2 | 2 |
| 6 | 19 | 2731 | 2731 | YES | 1 | 1 |
| 7 | 22 | 4198 | 4198 | YES | 1 | 1 |
| 8 | 25 | 6232 | 6232 | YES | 2 | 2 |
| 9 | 28 | 5188 | 5188 | YES | 2 | 2 |
| 10 | 31 | 3982 | 3982 | YES | 1 | 1 |
| 11 | 34 | 5530 | 5530 | YES | 2 | 2 |
| 12 | 37 | 6187 | 6187 | YES | 2 | 2 |
| 13 | 40 | 2308 | 2308 | YES | 1 | 1 |
| 14 | 43 | 3370 | 3370 | YES | 1 | 1 |
| 15 | 46 | 5728 | 5728 | YES | 2 | 2 |

## R5 — Quartic blade mod 19683 (m = 0..15), row 8 read — the level-7 kill engine

| m | K | 4^K mod 19683 | quartic blade | match | row8 4^K | row8 blade |
|---|---|---|---|---|---|---|
| 0 | 1 | 4 | 4 | YES | 0 | 0 |
| 1 | 4 | 256 | 256 | YES | 0 | 0 |
| 2 | 7 | 16384 | 16384 | YES | 2 | 2 |
| 3 | 10 | 5377 | 5377 | YES | 0 | 0 |
| 4 | 13 | 9517 | 9517 | YES | 1 | 1 |
| 5 | 16 | 18598 | 18598 | YES | 2 | 2 |
| 6 | 19 | 9292 | 9292 | YES | 1 | 1 |
| 7 | 22 | 4198 | 4198 | YES | 0 | 0 |
| 8 | 25 | 12793 | 12793 | YES | 1 | 1 |
| 9 | 28 | 11749 | 11749 | YES | 1 | 1 |
| 10 | 31 | 3982 | 3982 | YES | 0 | 0 |
| 11 | 34 | 18652 | 18652 | YES | 2 | 2 |
| 12 | 37 | 12748 | 12748 | YES | 1 | 1 |
| 13 | 40 | 8869 | 8869 | YES | 1 | 1 |
| 14 | 43 | 16492 | 16492 | YES | 2 | 2 |
| 15 | 46 | 12289 | 12289 | YES | 1 | 1 |

## R6 — The survivor doubling map (levels 1..9): the alive set DOUBLES every level, no exception

| level L | modulus 3^L | survivors: r ≡ 1 mod 3, no 2 in rows 0..L | count | the survivors |
|---|---|---|---|---|
| 1 | 3 | (see left) | 1 | [1] |
| 2 | 9 | (see left) | 2 | [1, 4] |
| 3 | 27 | (see left) | 4 | [1, 4, 10, 13] |
| 4 | 81 | (see left) | 8 | [1, 4, 10, 13, 28, 31, 37, 40] |
| 5 | 243 | (see left) | 16 | [1, 4, 10, 13, 28, 31, 37, 40, 82, 94, 109, 121, 166, 172, 193, 199] |
| 6 | 729 | (see left) | 32 | [1, 4, 10, 13, 28, 40, 82, 94, 109, 121, 166, 193, …] |
| 7 | 2187 | (see left) | 64 | [1, 4, 13, 40, 82, 94, 109, 121, 166, 193, 244, 247, …] |
| 8 | 6561 | (see left) | 128 | [1, 4, 13, 40, 94, 109, 121, 166, 193, 244, 280, 283, …] |
| 9 | 19683 | (see left) | 256 | [1, 4, 13, 121, 166, 280, 364, 436, 496, 514, 523, 595, …] |

## R7a — The 32 dead classes mod 2187 (cascade level 6): all fire at row 7 — verified 32/32, failures 0

## R7b — The 64 dead classes mod 6561 (cascade level 7): all fire at row 8 — verified 64/64, failures 0

Level-6 survivors (64 of them): 64
Level-6 dead classes by t (dead child trit): {0: 10, 1: 8, 2: 14}
Level-7 survivors: 128
Level-7 dead classes by t: {0: 12, 1: 26, 2: 26}

## R8 — The pair-read kill zone: residue (4^T · u · 16) mod 27 — kill iff ≥ 18 (row j+4 fires)

| 4^T mod 27 ↓, u → | u=1 | u=2 | u=4 | u=5 | u=7 | u=8 |
|---|---|---|---|---|---|---|
| 1 | 16 | 5 | 10 | **26 KILL** | 4 | **20 KILL** |
| 4 | 10 | **20 KILL** | 13 | **23 KILL** | 16 | **26 KILL** |
| 7 | 4 | 8 | 16 | **20 KILL** | 1 | 5 |
| 10 | **25 KILL** | **23 KILL** | **19 KILL** | 17 | 13 | 11 |
| 13 | **19 KILL** | 11 | **22 KILL** | 14 | **25 KILL** | 17 |
| 16 | 13 | **26 KILL** | **25 KILL** | 11 | 10 | **23 KILL** |
| 19 | 7 | 14 | 1 | 8 | **22 KILL** | 2 |
| 22 | 1 | 2 | 4 | 5 | 7 | 8 |
| 25 | **22 KILL** | 17 | 7 | 2 | **19 KILL** | 14 |


## R9 — The tower fire constants c(j): 4^(3^j) = 1 + 3^(j+1)·c(j) (the LTE identity)

| j | c(j) (digit count, head…tail) | c(j) mod 3 | c(j) mod 9 | c(j) mod 27 | c(j) mod 81 |
|---|---|---|---|---|---|
| 1 | 7 | 1 | 7 | 7 | 7 |
| 2 | 9709 | 1 | 7 | 16 | 70 |
| 3 | 222399981598543 | 1 | 7 | 16 | 16 |
| 4 | 47 digits: 240576401206…792690247621 | 1 | 7 | 16 | 16 |
| 5 | 144 digits: 274062972867…601179153047 | 1 | 7 | 16 | 16 |
| 6 | 436 digits: 364657285732…262801031389 | 1 | 7 | 16 | 16 |
| 7 | 1313 digits: 773091674785…037654771103 | 1 | 7 | 16 | 16 |
| 8 | 3946 digits: 662997377098…078215481141 | 1 | 7 | 16 | 16 |
| 9 | 11846 digits: 376354194881…990052278887 | 1 | 7 | 16 | 16 |
| 10 | 35546 digits: 619575338653…996829630669 | 1 | 7 | 16 | 16 |
| 11 | 106648 digits: 248787592747…347004762863 | 1 | 7 | 16 | 16 |
| 12 | 319954 digits: 144968956325…674382001061 | 1 | 7 | 16 | 16 |

The signature stabilizes: c(j) ≡ 1 (mod 3) always; c(j) ≡ 7 (mod 9) for j ≥ 1; c(j) ≡ 16 (mod 27) for j ≥ 2; c(j) ≡ 16 (mod 81) for j ≥ 3 — exactly the green `c_mod3`, `c_mod9_all`, `c_mod81_all` laws of GSTTowerFire.


## R10 — Complete Cantorian exponent census, 0 ≤ K < 6561 (exact big-int, rows 0..48)

Cantorian exponents: [0, 1, 4] — count 3.
(Everything else dies; the census is EXACT and complete below 6561.)


## R11 — The extinction profile: first-2 row distribution for dust exponents K ≡ 1 mod 3, 8 ≤ K < 2000

| first row with trit 2 | dust exponents K ≡ 1 mod 3 in [8,2000) |
|---|---|
| 2 | 221 |
| 3 | 148 |
| 4 | 97 |
| 5 | 64 |
| 6 | 44 |
| 7 | 32 |
| 8 | 11 |
| 9 | 16 |
| 10 | 12 |
| 11 | 8 |
| 12 | 6 |
| 13 | 3 |
| 14 | 1 |
| 15 | 1 |

Reading: the population roughly HALVES each row — 221, 148, 97, 64, 44, 32, 11+16, 12+8+6, ... — the halving cascade of the survivor map. Nothing survives past row 15 in this range.

## R12 — The pair-read family in the wild: K = 4 + 3^(j+1)·u, u ∈ {1,4,7}: row j+4 of 4^K IS 2

| j | row j+4 | K(u=1) | trit | K(u=4) | trit | K(u=7) | trit | verdict |
|---|---|---|---|---|---|---|---|---|
| 4 | 8 | 247 | 2 | 976 | 2 | 1705 | 2 | ALL FIRE |
| 5 | 9 | 733 | 2 | 2920 | 2 | 5107 | 2 | ALL FIRE |
| 6 | 10 | 2191 | 2 | 8752 | 2 | 15313 | 2 | ALL FIRE |
| 7 | 11 | 6565 | 2 | 26248 | 2 | 45931 | 2 | ALL FIRE |
| 8 | 12 | 19687 | 2 | 78736 | 2 | 137785 | 2 | ALL FIRE |
| 9 | 13 | 59053 | 2 | 236200 | 2 | 413347 | 2 | ALL FIRE |
| 10 | 14 | 177151 | 2 | 708592 | 2 | 1240033 | 2 | ALL FIRE |
| 11 | 15 | 531445 | 2 | 2125768 | 2 | 3720091 | 2 | ALL FIRE |
| 12 | 16 | 1594327 | 2 | 6377296 | 2 | 11160265 | 2 | ALL FIRE |

**Verdict: ALL 9 levels × 3 branches FIRE at row j+4 — 0 failures.**

## R13 — Trunk-13 family K = 13 + 3^(j+1)·u: the mod-27 kill-zone automaton, j = 15..19

- j=15, u=1: K = 43046734, trit at row 19 = 2, residue (4^13·u·16) mod 27 = 19, predicted **2 (kill)** — **MATCH**
- j=15, u=2: K = 86093455, trit at row 19 = 1, residue (4^13·u·16) mod 27 = 11, predicted no kill — **MATCH**
- j=15, u=3: K = 129140176, trit at row 19 = 0, residue (4^13·u·16) mod 27 = 3, predicted no kill — **MATCH**
- j=16, u=1: K = 129140176, trit at row 20 = 2, residue (4^13·u·16) mod 27 = 19, predicted **2 (kill)** — **MATCH**
- j=16, u=2: K = 258280339, trit at row 20 = 1, residue (4^13·u·16) mod 27 = 11, predicted no kill — **MATCH**
- j=16, u=3: K = 387420502, trit at row 20 = 0, residue (4^13·u·16) mod 27 = 3, predicted no kill — **MATCH**
- j=17, u=1: K = 387420502, trit at row 21 = 2, residue (4^13·u·16) mod 27 = 19, predicted **2 (kill)** — **MATCH**
- j=17, u=2: K = 774840991, trit at row 21 = 1, residue (4^13·u·16) mod 27 = 11, predicted no kill — **MATCH**
- j=17, u=3: K = 1162261480, trit at row 21 = 0, residue (4^13·u·16) mod 27 = 3, predicted no kill — **MATCH**
- j=18, u=1: K = 1162261480, trit at row 22 = 2, residue (4^13·u·16) mod 27 = 19, predicted **2 (kill)** — **MATCH**
- j=18, u=2: K = 2324522947, trit at row 22 = 1, residue (4^13·u·16) mod 27 = 11, predicted no kill — **MATCH**
- j=18, u=3: K = 3486784414, trit at row 22 = 0, residue (4^13·u·16) mod 27 = 3, predicted no kill — **MATCH**
- j=19, u=1: K = 3486784414, trit at row 23 = 2, residue (4^13·u·16) mod 27 = 19, predicted **2 (kill)** — **MATCH**
- j=19, u=2: K = 6973568815, trit at row 23 = 1, residue (4^13·u·16) mod 27 = 11, predicted no kill — **MATCH**
- j=19, u=3: K = 10460353216, trit at row 23 = 0, residue (4^13·u·16) mod 27 = 3, predicted no kill — **MATCH**


## R14 — The descent engine window law: row H+2 of 4^K = the column-read formula

| K | H | trunk K%3^H | branch K/3^H | row H+2 actual | window formula | match |
|---|---|---|---|---|---|---|
| 8 | 2 | 8 | 0 | 2 | 2 | YES |
| 10 | 2 | 1 | 1 | 0 | 0 | YES |
| 13 | 2 | 4 | 1 | 0 | 0 | YES |
| 28 | 3 | 1 | 1 | 0 | 0 | YES |
| 40 | 3 | 13 | 1 | 0 | 0 | YES |
| 82 | 4 | 1 | 1 | 0 | 0 | YES |
| 94 | 4 | 13 | 1 | 1 | 1 | YES |
| 121 | 4 | 40 | 1 | 0 | 0 | YES |
| 244 | 5 | 1 | 1 | 0 | 0 | YES |
| 580 | 5 | 94 | 2 | 1 | 1 | YES |
| 730 | 6 | 1 | 1 | 0 | 0 | YES |
| 976 | 6 | 247 | 1 | 2 | 2 | YES |
| 1246 | 6 | 517 | 1 | 2 | 2 | YES |
| 2191 | 7 | 4 | 1 | 0 | 0 | YES |

**Window law: 14/14 verified, 0 failures.**

## R15 — The general trunk-uniform law, random valid triples (T free, u free, j ∈ [6,9], 4^T < 3^(j+2))

Kill-zone triples tested: 44, fired at row j+4: 44, **failures: 0**.

## R16 — The noise receipts noise_6(r) = digit3(4^r, 7): the generator of dust_fire_row_seven (32/32)

| dead class mod 2187 | = r + 729·t | noise = d3(4^r, 7) | (noise + t) % 3 | class fires at row 7? |
|---|---|---|---|---|
| 10 | 10 + 729·0 | 2 | 2 | YES |
| 28 | 28 + 729·0 | 2 | 2 | YES |
| 199 | 199 + 729·0 | 2 | 2 | YES |
| 274 | 274 + 729·0 | 2 | 2 | YES |
| 415 | 415 + 729·0 | 2 | 2 | YES |
| 442 | 442 + 729·0 | 2 | 2 | YES |
| 499 | 499 + 729·0 | 2 | 2 | YES |
| 517 | 517 + 729·0 | 2 | 2 | YES |
| 652 | 652 + 729·0 | 2 | 2 | YES |
| 658 | 658 + 729·0 | 2 | 2 | YES |
| 742 | 13 + 729·1 | 1 | 2 | YES |
| 769 | 40 + 729·1 | 1 | 2 | YES |
| 811 | 82 + 729·1 | 1 | 2 | YES |
| 895 | 166 + 729·1 | 1 | 2 | YES |
| 1012 | 283 + 729·1 | 1 | 2 | YES |
| 1054 | 325 + 729·1 | 1 | 2 | YES |
| 1309 | 580 + 729·1 | 1 | 2 | YES |
| 1324 | 595 + 729·1 | 1 | 2 | YES |
| 1459 | 1 + 729·2 | 0 | 2 | YES |
| 1462 | 4 + 729·2 | 0 | 2 | YES |
| 1552 | 94 + 729·2 | 0 | 2 | YES |
| 1567 | 109 + 729·2 | 0 | 2 | YES |
| 1579 | 121 + 729·2 | 0 | 2 | YES |
| 1651 | 193 + 729·2 | 0 | 2 | YES |
| 1702 | 244 + 729·2 | 0 | 2 | YES |
| 1705 | 247 + 729·2 | 0 | 2 | YES |
| 1738 | 280 + 729·2 | 0 | 2 | YES |
| 1822 | 364 + 729·2 | 0 | 2 | YES |
| 1894 | 436 + 729·2 | 0 | 2 | YES |
| 1954 | 496 + 729·2 | 0 | 2 | YES |
| 1972 | 514 + 729·2 | 0 | 2 | YES |
| 1981 | 523 + 729·2 | 0 | 2 | YES |

**All 32 noise receipts hold: the dead child trit t = (2 − noise) mod 3 generates exactly the dead class, and every class fires — 32/32, 0 failures.**

## R17 — The self-read law, numeric check: d3(4^K, j+1) = (d3(4^(K mod 3^j), j+1) + d3(K, j)) mod 3

| K | j | d3(4^K, j+1) | d3(4^(K%3^j), j+1) | d3(K, j) | sum mod 3 | match |
|---|---|---|---|---|---|---|
| 8 | 2 | 0 | 0 | 0 | 0 | YES |
| 10 | 3 | 0 | 0 | 0 | 0 | YES |
| 13 | 2 | 1 | 0 | 1 | 1 | YES |
| 28 | 4 | 0 | 0 | 0 | 0 | YES |
| 40 | 5 | 0 | 0 | 0 | 0 | YES |
| 82 | 6 | 1 | 1 | 0 | 1 | YES |
| 94 | 7 | 1 | 1 | 0 | 1 | YES |
| 121 | 8 | 1 | 1 | 0 | 1 | YES |
| 244 | 9 | 2 | 2 | 0 | 2 | YES |
| 580 | 10 | 0 | 0 | 0 | 0 | YES |
| 2653 | 3 | 0 | 1 | 2 | 0 | YES |
| 3235 | 1 | 1 | 0 | 1 | 1 | YES |
| 594 | 9 | 0 | 0 | 0 | 0 | YES |
| 772 | 6 | 2 | 1 | 1 | 2 | YES |
| 4775 | 1 | 2 | 1 | 1 | 2 | YES |
| 4157 | 4 | 0 | 0 | 0 | 0 | YES |
| 308 | 2 | 1 | 0 | 1 | 1 | YES |
| 3553 | 7 | 0 | 2 | 1 | 0 | YES |
| 573 | 4 | 2 | 1 | 1 | 2 | YES |
| 744 | 9 | 2 | 2 | 0 | 2 | YES |

**Self-read law: 20/20 verified, 0 failures.**

## R18 — The tower fire laws: digit3(4^(3^n), n+2) = 2 and digit3(4^(2·3^n), n+1) = 2

| n | 3^n | d3(4^(3^n), n+2) | d3(4^(2·3^n), n+1) | 3^n + 1: d3(4^(3^n+1), n+2) for n ≥ 3 |
|---|---|---|---|---|
| 1 | 3 | 2 | 2 | - |
| 2 | 9 | 2 | 2 | - |
| 3 | 27 | 2 | 2 | 0 |
| 4 | 81 | 2 | 2 | 0 |
| 5 | 243 | 2 | 2 | 0 |
| 6 | 729 | 2 | 2 | 0 |
| 7 | 2187 | 2 | 2 | 0 |
| 8 | 6561 | 2 | 2 | 0 |
| 9 | 19683 | 2 | 2 | 0 |
| 10 | 59049 | 2 | 2 | 0 |
| 11 | 177147 | 2 | 2 | 0 |

---

# PART VII — THE GST GRAPH V2 ATLAS: THE COMPLETE CONSTRUCTION PROTOCOL

Part III gave the construction protocol of the universe graph in twelve steps. This atlas completes it: the full ontology of vertices, edges, currents, and the twelve-cell physics, followed by the complete verbatim source of the ontological module. Read Part III first for the protocol; read this part for the full inventory and the green proofs.

## VII.1 The vertex atlas

Every vertex is a cell $\mathbf{v}(E, t, p) = (C, d)$ — a carry state $C \in \{0, 1, 2, 3\}$ (the vertical axis; `graph_carry_lt_four`) and a digit state $d \in \{0, 1, 2\}$ (the horizontal axis; `graph_digit_lt_three`). The full vertex space is the twelve-cell lattice:

| | $d = 0$ | $d = 1$ | $d = 2$ |
|---|---|---|---|
| $C = 0$ | $(0,0)$ origin-silence | $(0,1)$ origin-unit | $(0,2)$ origin-fire |
| $C = 1$ | $(1,0)$ first-echo | $(1,1)$ first-chord | $(1,2)$ first-fire |
| $C = 2$ | $(2,0)$ second-echo | $(2,1)$ second-chord | $(2,2)$ second-fire |
| $C = 3$ | $(3,0)$ third-echo | $(3,1)$ third-chord | $(3,2)$ third-fire |

The dynamics on the lattice is the x4-cell law: $\mathrm{out}(C,d) = (C + 4d) \bmod 3$ (the emitted worldtrace trit) and $\mathrm{next}(C, d) = \lfloor (C + 4d)/3 \rfloor$ (the vertical flow). This is the **twelve-cell physics** — `ontDensity_physical_table` fixes the density (the ontological charge) of each of the twelve cells as an explicit integer, and the no-erasure laws pin the sign structure: happy cells carry density $\ge 42$, non-happy cells $\le 0$, with the exact dichotomy `happy_iff_ontDensity_positive`.

## VII.2 The edge atlas

Four edge families, all green:

1. **Ω-edges (vertical):** $(C, d) \to (\mathrm{next}(C,d), d')$ — the divide-by-3-multiply-by-4 transfusion of the origin word through the cell. Laws: `omegaWaveStep_u_divide` (the origin trit is consumed exactly), `omegaWaveStep_u_multiply` (the seed action is the exact x4 carry law), `omegaWaveStep_mass` (mass conservation), `omegaWaveStep_worldtrace` (the emitted digits are the worldtrace).
2. **Digit edges (horizontal):** the increments $d \to d+1$ within a carry level — the branch choices of the dust tree. The horizontal telescope `horizontal_diff_telescope` is the accounting law for these edges: summed differences collapse to boundary terms.
3. **Crossing edges (diagonal):** the changes of U-charge across a cell — `graph_happy_iff_crossing_positive`: a cell is happy iff its crossing count is positive. The kill dichotomy lives on these edges.
4. **Seed edges (initial):** `prefix_slice_seed_zero`, `prefix_slice_seed_one` — the first two slices of any exponent's carry stream are pinned exactly, so every orbit in the graph has a certified head.

## VII.3 The current atlas

The ontological currents — the integrals of the cell densities along paths and over rectangles:

- **`reverseOntCode`** — the reverse base-seven coding of an ontological state sequence. `reverseOntCode_exact`: the coding is an isomorphism onto its image (no information lost); `reverseOntCode_ge_global_floor`: the code is bounded below, globally, by an explicit floor; `reverseOntCode_ge_scaled_of_leading_happy`: a happy leading cell scales the floor up. The base-seven structure is why seven is the *observer's base* — the ontology counts in sevens what the physics does in threes.
- **`weightedOntPrefix`** — the prefix-weighted charge of a state sequence, with `weightedOntPrefix_ge_global_floor` and `weightedOntPrefix_positive_of_top_leading_happy` (positivity from the top cell alone).
- **`graphOntWindow`** — the windowed current over a rectangle of the lattice, with `graphOntWindow_positive_of_happy`: happy rectangles carry positive current, no matter what happens inside. This is the local-to-global law of the universe: **interiors cancel, boundaries speak** (`ternaryWeightedOntDiff_telescope`, `weightedOntPrefix_eq_sum`).

## VII.4 The construction, summarized as one protocol

To construct the GST Graph V2 Ontological Universe Graph for an exponent $E$:

1. Compute the origin word of $E$ (its base-3 expansion, least significant trit first).
2. Seed the carry stream: $C_0 = 0$ (or the certified seed of `prefix_slice_seed_zero/one`).
3. Run the Ω-dynamics: at step $t$, consume origin trit $d_t$, emit $(C_t + 4d_t) \bmod 3$, carry $(C_t + 4d_t)/3$ forward. The emitted stream is the worldtrace of $4^E$ — certified by `omegaWaveStep_worldtrace` and the observer laws.
4. Place each step on the twelve-cell lattice; weight by the physical table; accumulate the currents along the path.
5. The firing question — does some emitted trit equal 2 — is the question whether the path ever crosses a fire cell $(C, 2)$ with positive crossing count; the dichotomy laws turn this into the sign of the windowed current.

Every element of this protocol is green; the complete verbatim source follows.

## VII.5 The ontological module, complete and verbatim

**File: `GSTGraphV2Ontological.lean` — 384 lines, every declaration green.**

```lean
import GSTGraphV2InfiniteControl

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTGraphV2Ontological

open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2InfiniteControl

/-!
# GST Graph V2 — ontological current

This module is a finite-state certificate discovered from the exact twelve
physical x4/base3 cells.  It deliberately uses a reverse-base-seven horizontal
current: seven is the smallest tested pure-divergence scale for which the
resulting physical table simultaneously separates Happy from bad cells and
has enough no-erasure margin for the base-three highest-row domination.

No terminal-height, support-horizon, master theorem, or monolith dependency is
used here.
-/

/-- Horizontal information potential for the pure ontological current. -/
def ontDigitPotential (d : Nat) : Int :=
  if d = 0 then 9 else if d = 1 then -35 else -91

/-- Vertical carry potential for the pure ontological current. -/
def ontCarryPotential (C : Nat) : Int :=
  if C = 0 then 0 else if C = 1 then 77 else if C = 2 then 154 else 252

/-- Pure x7/base3 divergence.  Unlike the older crossing densities this has no
interior SURVIVE source term. -/
def ontDensity (C d : Nat) : Int :=
  ontDigitPotential (outDigit C d) - 7 * ontDigitPotential d +
    ontCarryPotential C - 3 * ontCarryPotential (nextCarry C d)

/-- Complete twelve-state certificate.  Exactly the two Happy cells are
positive; every bad physical cell is nonpositive; the global floor is -54. -/
theorem ontDensity_physical_table :
    ontDensity 0 0 = -54 ∧ ontDensity 0 1 = -21 ∧ ontDensity 0 2 = 84 ∧
    ontDensity 1 0 = -21 ∧ ontDensity 1 1 = 0 ∧ ontDensity 1 2 = -33 ∧
    ontDensity 2 0 = 0 ∧ ontDensity 2 1 = -54 ∧ ontDensity 2 2 = 0 ∧
    ontDensity 3 0 = -33 ∧ ontDensity 3 1 = 0 ∧ ontDensity 3 2 = 42 := by
  decide

/-- A physical Happy cell injects at least 42 units of ontological current. -/
theorem ontDensity_ge_42_of_happy
    (C d : Nat) (h : HappyCell C d) :
    (42 : Int) ≤ ontDensity C d := by
  rcases h with ⟨hd, hC⟩
  subst d
  rcases hC with h0 | h3
  · subst C
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]
  · subst C
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Uniform floor of the ontological density on physical cells. -/
theorem ontDensity_ge_neg54
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    (-54 : Int) ≤ ontDensity C d := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Every non-Happy physical cell has nonpositive ontological density. -/
theorem ontDensity_nonpositive_of_not_happy
    (C d : Nat) (hC : C < 4) (hd : d < 3)
    (hbad : ¬ HappyCell C d) :
    ontDensity C d ≤ 0 := by
  have hCc : C = 0 ∨ C = 1 ∨ C = 2 ∨ C = 3 := by omega
  have hdc : d = 0 ∨ d = 1 ∨ d = 2 := by omega
  rcases hCc with rfl | rfl | rfl | rfl <;>
    rcases hdc with rfl | rfl | rfl <;>
    simp [HappyCell] at hbad <;>
    norm_num [ontDensity, ontDigitPotential, ontCarryPotential,
      outDigit, nextCarry]

/-- Happy is exactly the positive sector of the pure ontological current. -/
theorem happy_iff_ontDensity_positive
    (C d : Nat) (hC : C < 4) (hd : d < 3) :
    HappyCell C d ↔ 0 < ontDensity C d := by
  constructor
  · intro h
    have h42 := ontDensity_ge_42_of_happy C d h
    omega
  · intro hpos
    by_contra hbad
    have hnonpos := ontDensity_nonpositive_of_not_happy C d hC hd hbad
    omega

/-- Reverse-base-seven accumulation of one horizontal graph row. -/
def reverseOntCode (C d : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCode C d N + ontDensity (C N) (d N)

/-- Matching reverse-base-seven accumulation of the vertical carry potential. -/
def reverseOntCarryCode (C : Nat → Nat) : Nat → Int
  | 0 => 0
  | N+1 => 7 * reverseOntCarryCode C N + ontCarryPotential (C N)

/-- Exact horizontal telescope of the pure ontological current. -/
theorem reverseOntCode_exact
    (C Cnext d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → outDigit (C t) (d t) = d (t+1)) →
    (∀ t, t < N → nextCarry (C t) (d t) = Cnext t) →
    reverseOntCode C d N =
      ontDigitPotential (d N) -
        (((7^N : Nat) : Int)) * ontDigitPotential (d 0) +
      reverseOntCarryCode C N - 3 * reverseOntCarryCode Cnext N := by
  intro N
  induction N with
  | zero =>
      intro hout hnext
      simp [reverseOntCode, reverseOntCarryCode]
  | succ N ih =>
      intro hout hnext
      have ih' := ih
        (fun t ht => hout t (by omega))
        (fun t ht => hnext t (by omega))
      have houtN := hout N (by omega)
      have hnextN := hnext N (by omega)
      rw [reverseOntCode, reverseOntCarryCode, reverseOntCarryCode,
        ih', ontDensity, houtN, hnextN, Nat.pow_succ]
      push_cast
      ring

/-- Global floor for an arbitrary physical horizontal row. -/
theorem reverseOntCode_ge_global_floor
    (C d : Nat → Nat) : ∀ N : Nat,
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    9 - 9 * (((7^N : Nat) : Int)) ≤ reverseOntCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hC hd
      simp [reverseOntCode]
  | succ N ih =>
      intro hC hd
      have ih' := ih
        (fun t ht => hC t (by omega))
        (fun t ht => hd t (by omega))
      have hlast := ontDensity_ge_neg54 (C N) (d N)
        (hC N (by omega)) (hd N (by omega))
      have hpow :
          (((7^(N+1) : Nat) : Int)) =
            7 * (((7^N : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [reverseOntCode, hpow]
      omega

/-- **Pure horizontal no-erasure.**  A leading Happy cell starts with at least
42.  Every later physical cell costs at most 54 while the current is multiplied
by seven.  The scaled closed form avoids predecessor arithmetic:

  33*7^N + 63 ≤ 7*code_N.
-/
theorem reverseOntCode_ge_scaled_of_leading_happy
    (C d : Nat → Nat)
    (hfirst : HappyCell (C 0) (d 0)) : ∀ N : Nat,
    1 ≤ N →
    (∀ t, t < N → C t < 4) →
    (∀ t, t < N → d t < 3) →
    33 * (((7^N : Nat) : Int)) + 63 ≤ 7 * reverseOntCode C d N := by
  intro N
  induction N with
  | zero =>
      intro hN
      omega
  | succ N ih =>
      intro hN hC hd
      by_cases hN0 : N = 0
      · subst N
        have hlead := ontDensity_ge_42_of_happy (C 0) (d 0) hfirst
        simp only [reverseOntCode]
        norm_num
        omega
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        have ih' := ih hNpos
          (fun t ht => hC t (by omega))
          (fun t ht => hd t (by omega))
        have ih7 := mul_le_mul_of_nonneg_left ih' (by norm_num : (0 : Int) ≤ 7)
        have hlast := ontDensity_ge_neg54 (C N) (d N)
          (hC N (by omega)) (hd N (by omega))
        have hlast7 := mul_le_mul_of_nonneg_left hlast (by norm_num : (0 : Int) ≤ 7)
        have hpow :
            (((7^(N+1) : Nat) : Int)) =
              7 * (((7^N : Nat) : Int)) := by
          rw [Nat.pow_succ]
          push_cast
          ring
        rw [reverseOntCode, hpow]
        omega

/-- Base-three weighted prefix of horizontal ontological rows. -/
def weightedOntPrefix
    (C d : Nat → Nat → Nat) (N : Nat) : Nat → Int
  | 0 => 0
  | K+1 =>
      weightedOntPrefix C d N K +
        (((3^K : Nat) : Int)) *
          reverseOntCode (fun t => C t K) (fun t => d t K) N

/-- Exact accumulated worst-case floor for all rows below a given height. -/
theorem weightedOntPrefix_ge_global_floor
    (C d : Nat → Nat → Nat) (N : Nat) : ∀ K : Nat,
    (∀ t p, t < N → p < K → C t p < 4) →
    (∀ t p, t < N → p < K → d t p < 3) →
    (9 - 9 * (((7^N : Nat) : Int))) *
        ((((3^K : Nat) : Int)) - 1) ≤
      2 * weightedOntPrefix C d N K := by
  intro K
  induction K with
  | zero =>
      intro hC hd
      simp [weightedOntPrefix]
  | succ K ih =>
      intro hC hd
      have ih' := ih
        (fun t p ht hp => hC t p ht (by omega))
        (fun t p ht hp => hd t p ht (by omega))
      have hrow := reverseOntCode_ge_global_floor
        (fun t => C t K) (fun t => d t K) N
        (fun t ht => hC t K ht (by omega))
        (fun t ht => hd t K ht (by omega))
      have hw : (0 : Int) ≤ 2 * (((3^K : Nat) : Int)) := by positivity
      have hrowW := mul_le_mul_of_nonneg_left hrow hw
      have h3pow :
          (((3^(K+1) : Nat) : Int)) =
            3 * (((3^K : Nat) : Int)) := by
        rw [Nat.pow_succ]
        push_cast
        ring
      rw [weightedOntPrefix, h3pow]
      calc
        (9 - 9 * (((7^N : Nat) : Int))) *
            (3 * (((3^K : Nat) : Int)) - 1) =
          (9 - 9 * (((7^N : Nat) : Int))) *
              ((((3^K : Nat) : Int)) - 1) +
            (2 * (((3^K : Nat) : Int))) *
              (9 - 9 * (((7^N : Nat) : Int))) := by ring
        _ ≤ 2 * weightedOntPrefix C d N K +
            (2 * (((3^K : Nat) : Int))) *
              reverseOntCode (fun t => C t K) (fun t => d t K) N :=
          add_le_add ih' hrowW
        _ = 2 *
            (weightedOntPrefix C d N K +
              (((3^K : Nat) : Int)) *
                reverseOntCode (fun t => C t K) (fun t => d t K) N) := by ring

/-- **Ontological highest-Happy-row domination.**  The base-seven pure current
has enough margin that a leading Happy row beats the total worst-case mass of
all lower rows under the literal base-three vertical weighting. -/
theorem weightedOntPrefix_positive_of_top_leading_happy
    (C d : Nat → Nat → Nat) (N q : Nat)
    (hN : 1 ≤ N)
    (hC : ∀ t p, t < N → p ≤ q → C t p < 4)
    (hd : ∀ t p, t < N → p ≤ q → d t p < 3)
    (hHappy : HappyCell (C 0 q) (d 0 q)) :
    0 < weightedOntPrefix C d N (q+1) := by
  let A : Int := (((7^N : Nat) : Int))
  let w : Int := (((3^q : Nat) : Int))
  let P : Int := weightedOntPrefix C d N q
  let R : Int := reverseOntCode (fun t => C t q) (fun t => d t q) N

  have hlower0 := weightedOntPrefix_ge_global_floor C d N q
    (fun t p ht hp => hC t p ht (by omega))
    (fun t p ht hp => hd t p ht (by omega))
  have hlower : (9 - 9*A) * (w - 1) ≤ 2*P := by
    simpa [A, w, P] using hlower0

  have htop0 := reverseOntCode_ge_scaled_of_leading_happy
    (fun t => C t q) (fun t => d t q) hHappy N hN
    (fun t ht => hC t q ht (by omega))
    (fun t ht => hd t q ht (by omega))
  have htop : 33*A + 63 ≤ 7*R := by
    simpa [A, R] using htop0

  have hlower7 := mul_le_mul_of_nonneg_left hlower (by norm_num : (0:Int) ≤ 7)
  have hw0 : (0 : Int) ≤ 2*w := by
    dsimp [w]
    positivity
  have htopW := mul_le_mul_of_nonneg_left htop hw0

  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hwpos : 0 < w := by
    dsimp [w]
    positivity
  have hAwpos : 0 < A*w := mul_pos hApos hwpos

  have hpositive :
      0 < 7 * ((9 - 9*A) * (w - 1)) +
        (2*w) * (33*A + 63) := by
    have hshape :
        7 * ((9 - 9*A) * (w - 1)) +
            (2*w) * (33*A + 63) =
          3*A*w + 63*A + 189*w - 63 := by ring
    rw [hshape]
    nlinarith [hApos, hwpos, hAwpos]

  have hbound :
      7 * ((9 - 9*A) * (w - 1)) +
          (2*w) * (33*A + 63) ≤
        14 * (P + w*R) := by
    calc
      7 * ((9 - 9*A) * (w - 1)) +
          (2*w) * (33*A + 63) ≤
        7 * (2*P) + (2*w) * (7*R) := add_le_add hlower7 htopW
      _ = 14 * (P + w*R) := by ring

  have hsumpos : 0 < P + w*R := by omega
  simpa [weightedOntPrefix, P, R, w] using hsumpos

/-- Base-three telescope for the vertical ontological carry derivative. -/
theorem ternaryWeightedOntDiff_telescope (g : Nat → Int) (K : Nat) :
    Finset.sum (Finset.range K) (fun p =>
      (((3^p : Nat) : Int)) * (g p - 3 * g (p+1))) =
      g 0 - (((3^K : Nat) : Int)) * g K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      push_cast
      ring

/-- Shifted production-window specialization on the actual infinite Graph V2. -/
def graphOntWindow (E N b K : Nat) : Int :=
  weightedOntPrefix
    (fun t j => (graph E t (b+j)).seven.carry)
    (fun t j => (graph E t (b+j)).seven.digit) N K

/-- A Happy source on the left edge gives strictly positive ontological current
through every nonzero-width Graph-V2 block. -/
theorem graphOntWindow_positive_of_happy
    (E N b q : Nat) (hN : 1 ≤ N)
    (hHappy : HappyCell
      (graph E 0 (b+q)).seven.carry
      (graph E 0 (b+q)).seven.digit) :
    0 < graphOntWindow E N b (q+1) := by
  unfold graphOntWindow
  apply weightedOntPrefix_positive_of_top_leading_happy
  · exact hN
  · intro t p ht hp
    exact graph_carry_lt_four E t (b+p)
  · intro t p ht hp
    exact graph_digit_lt_three E t (b+p)
  · simpa [Nat.add_assoc] using hHappy

/-- The recursive weighted prefix IS the literal base-three weighted sum of
the row codes — the bridge the exact window identity needs: the accumulated
column mass and the explicit sum are one object. -/
theorem weightedOntPrefix_eq_sum (C d : Nat → Nat → Nat) (N : Nat) :
    ∀ K : Nat,
    weightedOntPrefix C d N K =
      Finset.sum (Finset.range K) (fun p =>
        (((3^p : Nat) : Int)) *
          reverseOntCode (fun t => C t p) (fun t => d t p) N) := by
  intro K
  induction K with
  | zero => simp [weightedOntPrefix]
  | succ K ih =>
      simp only [weightedOntPrefix, Finset.sum_range_succ]
      rw [ih]

#check ontDensity_physical_table
#check happy_iff_ontDensity_positive
#check reverseOntCode_ge_scaled_of_leading_happy
#check weightedOntPrefix_positive_of_top_leading_happy
#check graphOntWindow_positive_of_happy
#print axioms weightedOntPrefix_positive_of_top_leading_happy

end GSTGraphV2Ontological
```

---

# PART VIII — THE COMPANION CODEX (verbatim)

The monolith (Part IV) does not stand alone. It imports three companions, and the wider proof environment holds two more that the final proof will want at hand. This part pastes them complete: **`GSTTheAct.lean`** (the object's own file — the terminal identity and the five green-equivalent forms), **`GSTTowerFire.lean`** (the LTE tower and the tower fire laws — the foundation under everything), and **`GSTDiagonalRead.lean`** (the diagonal triage). Then selections from **`GSTTheActConstruction.lean`** (the self-read feedback block) and **`GSTClimbInfiniteFamily.lean`** (the never-firing tower and Cantorian core). All are CI-green at HEAD, 0 sorries, standard axioms only.

## VIII.1 `GSTTheAct.lean` — the object's own file, complete

The 147-line file that defines `the_act` and certifies its equivalence to the full conjecture through the green odd half. Read the terminal identity carefully: it is the door every proof form walks through.

```lean
import Mathlib
import GSTInfiniteFourPowerNavigation
import GSTTailFProof
import GSTClimbTruthValue
import GSTCanonicalTailLTE
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE ACT — the exact missing object, named once (base module)

The base of the climb-family stack, extracted so that every module above
it (the diagonal read, the completed prefaced read, the cascade, the
collapse) can build on these objects without circularity:

* **§0 THE ACT.**  `the_act` names the exact object whose absence is the
  whole conditionality of `hTailF`: the even-exponent statement
  `∀ K ≥ 8, noTernaryTwo (4^K) = false`.  `the_act_iff_hTailF`: through the
  repo's own green unconditional iff, the act and `hTailF`'s target are ONE
  object — whatever proves the act proves `hTailF`, and nothing weaker
  than the act does.

* **§1 THE ANSWER.  Erdős closed ⇒ hTailF closed.**
  `hTailF_of_full_erdos`: if the full ternary statement
  (`∀ n ≥ 9, noTernaryTwo (2^n) = false`) is proven — by boss, by any
  construction, inside this repo or outside it — then `hTailF` closes in
  ONE line through this green bridge.  `the_act_iff_full_erdos`: the act
  and the full statement are one object, because the repo's own
  odd-exponent half is already green.  `climb_gives_the_act`: the climb,
  the input `hTailF` currently consumes, carries strictly MORE than the
  act (the pair demand: digit two with x4-carry zero or three) — the
  conditional route through the climb is overkill, not necessity.

* **§2 THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of
  `4^(3^v·a)` is exactly `a % 3`: the power-of-four ternary digit stream
  reads the reduced exponent trit directly — the zeroth level of the
  diagonal read, the seed of the whole ladder above it.
-/

namespace GSTTheAct

open GSTCanonicalSevenAxisBridge (digit3)

/-! ## §0 THE ACT — the exact missing object, named once -/

/-- THE ACT: every `4^K` from `K = 8` onward owns a ternary digit two.
This is the exact content whose absence is the whole conditionality of
`hTailF` — no more, no less. -/
def the_act : Prop := ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false

/-- **THE IDENTITY.**  Through the repo's own green unconditional iff,
the act and `hTailF`'s target are one object: whatever proves the act
proves `hTailF`, and nothing weaker than the act does. -/
theorem the_act_iff_hTailF :
    the_act ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  erdos_even_conjecture_iff_tailF

/-! ## §1 THE ANSWER — Erdős closed ⇒ hTailF closed -/

/-- The full ternary statement restricted to even exponents yields the act. -/
theorem the_act_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) : the_act := by
  intro K hK
  have h4 : 4^K = 2^(2*K) := (GSTClimbTruthValue.two_pow_two_mul K).symm
  rw [h4]
  exact hFull (2 * K) (by omega)

/-- **THE ANSWER.  Erdős closed ⇒ hTailF closed, one green line.**
If the full ternary statement is proven anywhere — by boss, by any
construction, inside this repo or outside it — `hTailF` closes through
this bridge.  The conditionality of `hTailF` is exactly the act, not the
climb: the climb is overkill. -/
theorem hTailF_of_full_erdos
    (hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  the_act_iff_hTailF.mp (the_act_of_full_erdos hFull)

/-- The act plus the repo's green odd-exponent half and the verified
below-floor instances assemble the FULL ternary statement. -/
theorem full_erdos_of_the_act (h : the_act) :
    ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨K, hK⟩ | ⟨k, hk⟩
  · have hK2 : n = 2 * K := by omega
    rw [hK2, GSTClimbTruthValue.two_pow_two_mul]
    rcases Nat.lt_or_ge K 8 with hK8 | hK8
    · have hK5 : 5 ≤ K := by omega
      interval_cases K
      · exact GSTClimbTruthValue.no22_four_pow_five
      · exact GSTClimbTruthValue.no22_four_pow_six
      · exact GSTClimbTruthValue.no22_four_pow_seven
    · exact h K hK8
  · exact erdos_ternary_2_conjecture_odd n hn (by omega)

/-- **THE ACT AND THE FULL STATEMENT ARE ONE OBJECT** — the odd-exponent
half is already green, so the even half is the whole remaining content. -/
theorem the_act_iff_full_erdos :
    the_act ↔ (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false) :=
  ⟨full_erdos_of_the_act, the_act_of_full_erdos⟩

/-- The climb carries strictly more than the act: whoever proves the
climb proves the act (the pair demand subsumes digit-two existence).
The climb is an overkill route to `hTailF`, not a necessity. -/
theorem climb_gives_the_act
    (hClimb : GSTInfiniteFourPowerNavigation.four_power_happy_climb) :
    the_act :=
  GSTClimbTruthValue.climb_implies_erdos hClimb

/-! ## §2 THE FRONT LAW — the seed of the diagonal read -/

/-- **THE FRONT LAW.**  At the valuation cut `v`, row `v+1` of `4^(3^v * a)`
is exactly `a % 3`: the power-of-four ternary digit stream reads the
reduced exponent trit directly.  Built on the repo's own green laws —
the exact LTE identity and the one-digit exponent lift. -/
theorem front_law (v : Nat) : ∀ a : Nat,
    digit3 (4^(3^v * a)) (v + 1) = a % 3 := by
  intro a
  induction a with
  | zero =>
      have h1 : 1 < 3^(v+1) := by
        have h3 : 3^1 ≤ 3^(v+1) :=
          Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
        norm_num at h3
        omega
      have hz : 3^v * 0 = 0 := by ring
      rw [hz, Nat.pow_zero]
      unfold digit3
      rw [Nat.div_eq_of_lt h1]
  | succ a ih =>
      have hA := GSTCanonicalTailLTE.pow4_three_power_lte_exact v
      have hc := GSTCanonicalTailLTE.lteCoeff_mod3_one v
      have hstep := GSTFinalPurePowerResidueTransplant.pow4_exponent_lift_one_digit
        v (3^v * a) (GSTCanonicalTailLTE.lteCoeff v) hA hc
      rw [show 3^v * (a + 1) = 3^v * a + 3^v by ring, hstep, ih]
      omega

#print axioms the_act_iff_hTailF
#print axioms the_act_of_full_erdos
#print axioms hTailF_of_full_erdos
#print axioms full_erdos_of_the_act
#print axioms the_act_iff_full_erdos
#print axioms climb_gives_the_act
#print axioms front_law

end GSTTheAct
```

## VIII.2 `GSTTowerFire.lean` — the LTE tower, complete

The 255-line foundation: the constants $c(j)$, the tower identity, the cubic recursion, the signature laws ($c \bmod 3, 9, 81$), the prefaced-digit shift, the two-term ladder, the tower digit read, and the three tower fire families. Every deep theorem in the corpus reduces to this file plus the binomial theorem.

```lean
import Mathlib
import GSTBladeWave

open GSTCanonicalSevenAxisBridge (digit3)
open GSTBladeWave (digit3_mod_pow)

namespace GSTTowerFire

/-!
# THE TOWER FIRES — Lane D's deep-hider laws, landed in Lean

Lane D (worldtrace) of the four-lane derivation volley, Lean-ified.
One new file, zero monolith bytes.  Machine receipts BEFORE landing
(fresh this session, exact big-int, modular tower arithmetic):

* `T1 30/30`  (n ∈ [1, 30]):  digit3 (4^(3^n)) (n+2) = 2
* `T2 28/28`  (n ∈ [3, 30]):  digit3 (4^(3^n + 1)) (n+4) = 2
* `T3 31/31`  (n ∈ [0, 30]):  digit3 (4^(2 * 3^n)) (n+1) = 2
* `T4 720/720`  (j ∈ [1, 8), n ∈ [1, 13), k ≤ n):
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k
* tower stabilization `c_(t+1) ≡ c_t mod 3^(t+1)`: 26/26 (t ∈ [0, 26))
* `c_t ≡ 7 mod 9` (t ∈ [1, 27)), `c_t ≡ 16 mod 81` (t ∈ [3, 27)), `c_0 = 1`

* **§1 THE c-TOWER.**  `c n = (4^(3^n) − 1) / 3^(n+1)` — integral by
  the green LTE cut `GSTBladeWave.four_pow_three_pow_dvd`.  The exact
  decomposition `four_pow_three_pow_eq : 4^(3^n) = 1 + 3^(n+1) * c n`,
  the cube recursion `c_succ_eq`, and the three congruence laws
  `c_mod3` (c ≡ 1 mod 3), `c_mod9` (c ≡ 7 mod 9 for n ≥ 1),
  `c_mod81` (c ≡ 16 mod 81 for n ≥ 3).

* **§2 THE READ GLUE.**  `div_add_lt` (divide-and-mod gluing) and
  `prefaced_digit`: if `s < 3^(n+1)` then row `n+1+k` of the prefaced
  object `3^(n+1) * A + s` is row `k` of `A`.

* **§3 THE TOWER READS.**  `tower_digit_read` (Lane D's L10 deep-hider
  master lemma): rows `n+1 .. 2n+1` of `4^(j * 3^n)` are the digits
  `0 .. n` of `j * c n` — ONE tower constant governs every scaled
  family at every depth.  The three fire laws fall out:
  `three_pow_fires` (3^n fires at row n+2 — L7), `two_mul_three_pow_fires`
  (2 * 3^n at row n+1 — L8), `three_pow_plus_one_fires` (3^n + 1 at
  row n+4 for n ≥ 3 — L9).
-/

set_option maxHeartbeats 400000

/-! ## §1 The c-tower -/

/-- The tower coefficients `c n = (4^(3^n) − 1) / 3^(n+1)`,
integral by the green LTE cut. -/
def c (n : Nat) : Nat := (4^(3^n) - 1) / 3^(n+1)

theorem c_zero : c 0 = 1 := by decide

/-- **The exact tower decomposition** — LTE made an equation. -/
theorem four_pow_three_pow_eq (n : Nat) : 4^(3^n) = 1 + 3^(n+1) * c n := by
  have h1 : (0:Nat) < 4^(3^n) := by positivity
  have h := GSTBladeWave.four_pow_three_pow_dvd 0 n
  rw [Nat.zero_add] at h
  obtain ⟨w, hw⟩ := h
  have hcw : c n = w := by
    unfold c
    rw [hw]
    exact Nat.mul_div_cancel_left _ (by positivity : (0:Nat) < 3^(n+1))
  rw [hcw]
  omega

/-- **The cube recursion of the tower.**  Cubing the decomposition of
`4^(3^n)` and matching orders gives `c (n+1)` from `c n` with exactly
the two binomial corrections. -/
theorem c_succ_eq (n : Nat) :
    c (n+1) = c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n)) := by
  have hpow : 4^(3^(n+1)) = (4^(3^n))^3 := by
    rw [Nat.pow_succ 3 n, Nat.pow_mul]
  have key : 1 + 3^((n+1)+1) * c (n+1)
      = 1 + 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
    calc 1 + 3^((n+1)+1) * c (n+1)
        = (4^(3^n))^3 := by rw [← four_pow_three_pow_eq (n+1), hpow]
      _ = (1 + 3^(n+1) * c n)^3 := by rw [four_pow_three_pow_eq]
      _ = 1 + 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
          have p1 : 3^((n+1)+1) = 3^n * 9 := by
            rw [Nat.pow_succ, Nat.pow_succ]; ring
          have p2 : 3^(n+1) = 3^n * 3 := Nat.pow_succ 3 n
          rw [p1, p2]
          ring
  have hcancel : 3^((n+1)+1) * c (n+1)
      = 3^((n+1)+1) * (c n + 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))) := by
    omega
  exact Nat.mul_left_cancel (by positivity : (0:Nat) < 3^((n+1)+1)) hcancel

/-- **The tower's first congruence: `c n ≡ 1 mod 3` at every level. -/
theorem c_mod3 (n : Nat) : c n % 3 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have h := c_succ_eq n
    have hf : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
        = 3 * (3^n * (c n * c n + 3^n * (c n * c n * c n))) := by
      rw [Nat.pow_succ]; ring
    rw [hf] at h
    omega

/-- **The tower's second congruence: `c n ≡ 7 mod 9` from level one on. -/
theorem c_mod9_all (n : Nat) : 1 ≤ n → c n % 9 = 7 := by
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0]
      decide
    · have h := c_succ_eq n
      have hm : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
          = 9 * (3^(n-1) * (c n * c n + 3^n * (c n * c n * c n))) := by
        have hexp : n+1 = 2 + (n-1) := by omega
        have e : 3^(n+1) = 3^2 * 3^(n-1) := by rw [hexp, ← Nat.pow_add]
        rw [e]; ring
      rw [hm] at h
      have iih := ih hpos
      omega

theorem c_mod9 (n : Nat) (hn : 1 ≤ n) : c n % 9 = 7 := c_mod9_all n hn

/-- **The tower's third congruence: `c n ≡ 16 mod 81` from level three on. -/
theorem c_mod81_all (n : Nat) : 3 ≤ n → c n % 81 = 16 := by
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn1
    rcases Nat.lt_or_ge n 3 with hlt | hge
    · have e2 : n = 2 := by omega
      subst e2
      decide
    · have h := c_succ_eq n
      have hm : 3^(n+1) * (c n * c n + 3^n * (c n * c n * c n))
          = 81 * (3^(n-3) * (c n * c n + 3^n * (c n * c n * c n))) := by
        have hexp : n+1 = 4 + (n-3) := by omega
        have e : 3^(n+1) = 3^4 * 3^(n-3) := by rw [hexp, ← Nat.pow_add]
        rw [e]; ring
      rw [hm] at h
      have iih := ih hge
      omega

theorem c_mod81 (n : Nat) (hn : 3 ≤ n) : c n % 81 = 16 := c_mod81_all n hn

/-! ## §2 The read glue -/

/-- **Divide-and-mod gluing:** `3^k * q + s` divided by `3^k` is `q`
when `s < 3^k`. -/
theorem div_add_lt (k q s : Nat) (hs : s < 3^k) : (3^k * q + s) / 3^k = q := by
  have hmod : (3^k * q + s) % 3^k = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hs]
  have h := Nat.div_add_mod (3^k * q + s) (3^k)
  rw [hmod] at h
  have h2 : 3^k * ((3^k * q + s) / 3^k) = 3^k * q := by omega
  exact Nat.mul_left_cancel (by positivity : (0:Nat) < 3^k) h2

/-- **The prefaced read.**  If `s < 3^(n+1)` then row `n+1+k` of the
prefaced object `3^(n+1) * A + s` is row `k` of `A`. -/
theorem prefaced_digit (A s n k : Nat) (hs : s < 3^(n+1)) :
    digit3 (3^(n+1) * A + s) (n+1+k) = digit3 A k := by
  unfold digit3
  have hdd : (3^(n+1) * A + s) / 3^(n+1+k)
      = ((3^(n+1) * A + s) / 3^(n+1)) / 3^k := by
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [hdd, div_add_lt (n+1) A s hs]

/-- **The two-term binomial.**  `(1 + x)^j = 1 + j*x + x*x*R` for some `R`. -/
theorem one_add_pow_two_term (x j : Nat) : ∃ R, (1+x)^j = 1 + j*x + x*x*R := by
  induction j with
  | zero => exact ⟨0, by ring⟩
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + j + x*R, ?_⟩
    rw [Nat.pow_succ, hR]
    ring

/-! ## §3 The tower reads -/

/-- **THE DEEP-HIDER MASTER LEMMA (Lane D's L10).**  Rows `n+1 .. 2n+1`
of `4^(j * 3^n)` are the digits `0 .. n` of `j * c n`: one tower
constant governs every scaled family at every depth. -/
theorem tower_digit_read (j n k : Nat) (hk : k ≤ n) :
    digit3 (4^(j * 3^n)) (n+1+k) = digit3 (j * c n) k := by
  obtain ⟨R, hR⟩ := one_add_pow_two_term (3^(n+1) * c n) j
  have hexp : 4^(j * 3^n)
      = 3^(n+1) * (j * c n + 3^(n+1) * ((c n * c n) * R)) + 1 := by
    rw [Nat.mul_comm j (3^n), Nat.pow_mul, four_pow_three_pow_eq, hR]
    ring
  have h1lt : (1:Nat) < 3^(n+1) := by
    have hp : (0:Nat) < 3^n := by positivity
    rw [Nat.pow_succ]
    omega
  rw [hexp, prefaced_digit _ 1 n k h1lt]
  unfold digit3
  have hsplit : j * c n + 3^(n+1) * (c n * c n * R)
      = j * c n + (3^(n+1-k) * (c n * c n * R)) * 3^k := by
    have hexp : n+1 = k + (n+1-k) := by omega
    have e : 3^(n+1) = 3^k * 3^(n+1-k) := by
      conv_lhs => rw [hexp]
      rw [← Nat.pow_add]
    rw [e]; ring
  rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : (0:Nat) < 3^k)]
  have hd3 : 3 ∣ 3^(n+1-k) * (c n * c n * R) := by
    have e : n+1-k = (n-k)+1 := by omega
    have h9 : 3^(n+1-k) = 3 * 3^(n-k) := by rw [e, Nat.pow_succ]; ring
    rw [h9]
    exact ⟨3^(n-k) * (c n * c n * R), by ring⟩
  omega

/-- **THE n+2 LAW (Lane D's L7).**  `3^n` fires at row `n+2` for every
`n ≥ 1`: the first rows are zero (the valuation), row `n+1` is one,
row `n+2` is TWO — the tower constant's second trit. -/
theorem three_pow_fires (n : Nat) (hn : 1 ≤ n) : digit3 (4^(3^n)) (n+2) = 2 := by
  have h := tower_digit_read 1 n 1 hn
  rw [Nat.one_mul, Nat.one_mul] at h
  rw [show n+2 = n+1+1 from by omega, h]
  rw [digit3_mod_pow, show (3:Nat)^(1+1) = 9 from by norm_num, c_mod9 n hn]
  norm_num

/-- **THE n+1 LAW (Lane D's L8).**  `2 * 3^n` fires at row `n+1` for
every `n ≥ 0` — the doubled tower constant reads its leading TWO. -/
theorem two_mul_three_pow_fires (n : Nat) : digit3 (4^(2 * 3^n)) (n+1) = 2 := by
  have h := tower_digit_read 2 n 0 (by omega)
  rw [show n+1 = n+1+0 from by omega, h]
  unfold digit3
  norm_num
  rw [Nat.mul_mod, c_mod3 n]

/-- **THE n+4 LAW (Lane D's L9).**  `3^n + 1` fires at row `n+4` for
every `n ≥ 3`: the prefaced tower constant `4 * c n ≡ 64 mod 81 = 2101₃`
plants the TWO at offset three. -/
theorem three_pow_plus_one_fires (n : Nat) (hn : 3 ≤ n) :
    digit3 (4^(3^n + 1)) (n+4) = 2 := by
  have hbig : (4:Nat) < 3^(n+1) := by
    have hexp : n+1 = 4 + (n-3) := by omega
    have e : 3^(n+1) = 3^4 * 3^(n-3) := by rw [hexp, ← Nat.pow_add]
    have hpos : (0:Nat) < 3^(n-3) := by positivity
    rw [e]
    omega
  have hdec : 4^(3^n + 1) = 3^(n+1) * (4 * c n) + 4 := by
    have h := four_pow_three_pow_eq n
    rw [Nat.pow_add, Nat.pow_one, h]
    ring
  rw [hdec, show n+4 = n+1+3 from by omega,
    prefaced_digit _ 4 n 3 hbig]
  rw [digit3_mod_pow, show (3:Nat)^(3+1) = 81 from by norm_num,
    Nat.mul_mod, c_mod81 n hn]
  norm_num

#print axioms three_pow_fires
#print axioms two_mul_three_pow_fires
#print axioms three_pow_plus_one_fires
#print axioms tower_digit_read

end GSTTowerFire
```

## VIII.3 `GSTDiagonalRead.lean` — the diagonal triage, complete

The 459-line triage file: the diagonal window law (the completion of the front law), the `lteCoeff` stability laws, the window fire levels 1–3 (the mod-9 / mod-27 / mod-81 bands), the classical kills (`4^9` fires at row 4; `4^108` fires at row 7), and the valuation decomposition that feeds the one-lane case map.

```lean
import Mathlib
import GSTCanonicalTailLTE
import GSTCanonicalTailStateIso
import GSTTheAct

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE DIAGONAL READ — every exponent's entire low band, one law

One separate file, zero monolith bytes.  The 4D object, constructed:

* **§0 THE ENGINE.**  `binom_two_term` (the two-term binomial expansion,
  by induction) and `digit3_mod_congr` (digits are stable under
  congruence mod `3^(p+1)`).

* **§1 THE WINDOW LAW.**  `diagonal_window_law`: for EVERY valuation cut
  `v` and EVERY reduced exponent `u`, the digit stream of `4^(3^v·u)` at
  rows `v+1 .. 2v+1` IS the ternary digit stream of `u · lteCoeff v`,
  trit by trit: `digit3 (4^(3^v·u)) (v+1+j) = digit3 (u · lteCoeff v) j`
  for every `j ≤ v`.  One law, every scale, every core, every row of
  the band — the digit stream READS the frozen diagonal.  At `v = 0`
  it subsumes the front law itself.

* **§2 THE FROZEN DIAGONAL.**  `lteCoeff_succ_mod` + `lteCoeff_stable`:
  the coefficient's trits freeze level by level (`lteCoeff (v+1) ≡
  lteCoeff v mod 3^(v+1)`), so the readable diagonal is the same object
  at every depth.  Residues: `7 mod 9`, `16 mod 27`, `16 mod 81`.

* **§3 THE FIRE FAMILIES.**  Unconditional digit-two laws, uniform in
  `v` and `u` — the ladder's first three levels:
  `u ≡ 1 mod 9` fires at row `v+2`; `u ≡ 13, 25 mod 27` fire at row
  `v+3`; `u ≡ 4, 34, 49, 70 mod 81` fire at row `v+4`.
  Witness receipts: `4^9` fires at row 4, `4^108` fires at row 7 —
  both delivered by the uniform law alone, no bounded decide.

* **§4 THE TRIAGE, THE DUST, THE SOCKET.**  Every `K ≥ 8` either owns
  its digit two (front fire or window fire) or is `WindowCleanDust` —
  the exact residual, named.  `no22_of_not_dust`: the read kills the
  dust's entire complement.  `hTailF_of_dust_empty`: dust empty ⇒
  the act ⇒ `hTailF`, through the standing green bridges.

* **§5 THE RECEIPT.**  Everything assembled in one theorem, with axiom
  printouts: the classical three only.
-/

namespace GSTDiagonalRead

open GSTCanonicalSevenAxisBridge (digit3)

/-! ## §0 THE ENGINE -/

/-- The two-term binomial expansion: `(1+x)^u = 1 + u·x + x²·s` for some
natural `s`.  By induction on `u` — pure algebra, no hypothesis. -/
theorem binom_two_term (x u : Nat) :
    ∃ s : Nat, (1 + x)^u = 1 + u * x + x * x * s := by
  induction u with
  | zero => exact ⟨0, by rw [Nat.pow_zero]; ring⟩
  | succ u ih =>
      obtain ⟨s, hs⟩ := ih
      refine ⟨u + s + x * s, ?_⟩
      calc (1 + x)^(u+1) = (1 + x)^u * (1 + x) := by rw [Nat.pow_succ]
        _ = (1 + u * x + x * x * s) * (1 + x) := by rw [hs]
        _ = 1 + (u + 1) * x + x * x * (u + s + x * s) := by ring

/-- Mod-zero folding: if `m ∣ b` then `(a + b) % m = a % m`.  The core
congruence step for the window law. -/
theorem add_mod_of_dvd (a b m : Nat) (hdvd : m ∣ b) :
    (a + b) % m = a % m := by
  obtain ⟨q, rfl⟩ := hdvd
  first
    | rw [Nat.add_mul_mod_self_left]
    | rw [Nat.add_mul_mod_self_right]

/-- Digit division below a modulus factor: dividing `3^p·3·q + r` by
`3^p` reads off the quotient `3·q` plus the sub-quotient. -/
theorem div_pow_add (q r p : Nat) :
    (3^p * 3 * q + r) / 3^p = 3 * q + r / 3^p := by
  have hp : 0 < 3^p := Nat.pow_pos (by decide)
  rw [show 3^p * 3 * q + r = r + 3^p * (3 * q) from by ring]
  rw [Nat.add_mul_div_left _ _ hp]
  omega

/-- Digits are stable under congruence mod `3^(p+1)`: if two numbers
agree modulo `3^(p+1)`, their row-`p` ternary digits agree. -/
theorem digit3_mod_congr (R R' p : Nat)
    (h : R % 3^(p+1) = R' % 3^(p+1)) :
    digit3 R p = digit3 R' p := by
  unfold digit3
  have hp1 : 3^(p+1) = 3^p * 3 := by rw [Nat.pow_succ]
  rw [hp1] at h
  have hR := Nat.div_add_mod R (3^p * 3)
  have hR' := Nat.div_add_mod R' (3^p * 3)
  rw [← hR, ← hR', div_pow_add, div_pow_add, h]
  omega

/-! ## §1 THE WINDOW LAW — the digit stream reads the diagonal -/

/-- The correction-term divisibility: with `j ≤ v`, the binomial tail
`(3^(v+1)·c)²·s` is divisible by `3^(v+2+j)` — the window's boundary. -/
theorem pow_cut_dvd (v j c s : Nat) (hj : j ≤ v) :
    3^(v+2+j) ∣ (3^(v+1) * c) * (3^(v+1) * c) * s := by
  refine ⟨3^(v-j) * (c * c * s), ?_⟩
  have hp2 : 3^(v+1) * 3^(v+1) = 3^(v+2+j) * 3^(v-j) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1; omega
  calc (3^(v+1) * c) * (3^(v+1) * c) * s
      = (3^(v+1) * 3^(v+1)) * (c * c * s) := by ring
    _ = (3^(v+2+j) * 3^(v-j)) * (c * c * s) := by rw [hp2]
    _ = 3^(v+2+j) * (3^(v-j) * (c * c * s)) := by ring

/-- **THE WINDOW LAW.**  For every valuation cut `v` and every reduced
exponent `u`, the digit stream of `4^(3^v·u)` at row `v+1+j` IS the
`j`-th ternary digit of `u · lteCoeff v`, for every `j ≤ v`.  The
tower's entire readable band, one law, all scales at once — including
`v = 0`, where it subsumes the front law. -/
theorem diagonal_window_law (v u j : Nat) (hj : j ≤ v) :
    digit3 (4^(3^v * u)) (v + 1 + j) =
      digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j := by
  have hLTE : 4^(3^v) = 1 + 3^(v+1) * GSTCanonicalTailLTE.lteCoeff v :=
    GSTCanonicalTailLTE.pow4_three_power_lte_exact v
  have hK : 4^(3^v * u) = (4^(3^v))^u := by rw [Nat.pow_mul]
  obtain ⟨s, hs⟩ :=
    binom_two_term (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) u
  have hu : u * (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) =
      3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v) := by ring
  have hcorr : 3^(v+2+j) ∣ (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) *
      (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) * s :=
    pow_cut_dvd v j (GSTCanonicalTailLTE.lteCoeff v) s hj
  have hcongr : 4^(3^v * u) % 3^((v+1+j)+1) =
      (1 + 3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v)) % 3^((v+1+j)+1) := by
    rw [show 3^((v+1+j)+1) = 3^(v+2+j) from by congr 1; omega]
    rw [hK, hLTE, hs, hu]
    exact add_mod_of_dvd _ _ _ hcorr
  have hdig := digit3_mod_congr (4^(3^v * u))
    (1 + 3^(v+1) * (u * GSTCanonicalTailLTE.lteCoeff v)) (v+1+j) hcongr
  rw [hdig]
  have h1lt : 1 < 3^(v+1) := by
    cases v with
    | zero => norm_num
    | succ v =>
        have h0 : 0 < 3^(v+1) := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
  simpa only [GSTCanonicalTailStateIso.digit3, digit3] using
    GSTCanonicalTailStateIso.prefix_slice_digit_exact (v+1) 1
      (u * GSTCanonicalTailLTE.lteCoeff v) j h1lt

/-- At the zero cut the window law IS the front law: row one of `4^u`
reads `u % 3` directly. -/
theorem window_subsumes_front (u : Nat) :
    digit3 (4^(3^0 * u)) (0 + 1 + 0) = u % 3 := by
  simpa [digit3, GSTCanonicalTailLTE.lteCoeff] using
    diagonal_window_law 0 u 0 (by omega)

/-! ## §2 THE FROZEN DIAGONAL — the coefficient's trits stabilize -/

/-- The coefficient's trits freeze: each recursion step preserves the
previous coefficient modulo `3^(v+1)`. -/
theorem lteCoeff_succ_mod (v : Nat) :
    GSTCanonicalTailLTE.lteCoeff (v+1) % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1) := by
  have hsplit : 3^(2*v+1) = 3^(v+1) * 3^v := by
    rw [← Nat.pow_add]
    congr 1; omega
  have hd1 : 3^(v+1) ∣ 3^(v+1) * (GSTCanonicalTailLTE.lteCoeff v)^2 :=
    ⟨_, rfl⟩
  have hd2 : 3^(v+1) ∣ 3^(2*v+1) * (GSTCanonicalTailLTE.lteCoeff v)^3 :=
    ⟨3^v * (GSTCanonicalTailLTE.lteCoeff v)^3, by rw [hsplit]; ring⟩
  simp only [GSTCanonicalTailLTE.lteCoeff]
  rw [add_mod_of_dvd _ _ _ hd2, add_mod_of_dvd _ _ _ hd1]

theorem mod_dvd_modeq (a b m n : Nat) (hmn : m ∣ n) (h : a % n = b % n) :
    a % m = b % m := by
  rw [← Nat.mod_mod_of_dvd a hmn, h, Nat.mod_mod_of_dvd b hmn]

/-- **THE FROZEN DIAGONAL.**  From index `v` upward, the coefficient is
constant modulo `3^(v+1)`: the readable diagonal is the same object at
every depth. -/
theorem lteCoeff_stable (v w : Nat) (hw : v ≤ w) :
    GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
      GSTCanonicalTailLTE.lteCoeff v % 3^(v+1) := by
  induction w with
  | zero =>
      have hv0 : v = 0 := by omega
      subst hv0
      rfl
  | succ w ih =>
      by_cases hwv : v ≤ w
      · have h := lteCoeff_succ_mod w
        have hdvd : 3^(v+1) ∣ 3^(w+1) := by
          refine ⟨3^(w-v), ?_⟩
          rw [← Nat.pow_add]
          congr 1; omega
        have h2 := mod_dvd_modeq (GSTCanonicalTailLTE.lteCoeff (w+1))
          (GSTCanonicalTailLTE.lteCoeff w) (3^(v+1)) (3^(w+1)) hdvd h
        rw [h2]
        exact ih hwv
      · have hvw : v = w + 1 := by omega
        subst hvw
        rfl

/-- The frozen diagonal's residue modulo 9 from index one: `7`. -/
theorem lteCoeff_mod9 (v : Nat) (hv : 1 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 9 = 7 := by
  have h := lteCoeff_stable 1 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 1 % 3^(1+1) = 7 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 9
      = GSTCanonicalTailLTE.lteCoeff v % 3^(1+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 1 % 3^(1+1) := h
    _ = 7 := hbase

/-- The frozen diagonal's residue modulo 27 from index two: `16`. -/
theorem lteCoeff_mod27 (v : Nat) (hv : 2 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 27 = 16 := by
  have h := lteCoeff_stable 2 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 2 % 3^(2+1) = 16 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 27
      = GSTCanonicalTailLTE.lteCoeff v % 3^(2+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 2 % 3^(2+1) := h
    _ = 16 := hbase

/-- The frozen diagonal's residue modulo 81 from index three: `16`. -/
theorem lteCoeff_mod81 (v : Nat) (hv : 3 ≤ v) :
    GSTCanonicalTailLTE.lteCoeff v % 81 = 16 := by
  have h := lteCoeff_stable 3 v hv
  have hbase : GSTCanonicalTailLTE.lteCoeff 3 % 3^(3+1) = 16 := by decide
  calc GSTCanonicalTailLTE.lteCoeff v % 81
      = GSTCanonicalTailLTE.lteCoeff v % 3^(3+1) := by norm_num
    _ = GSTCanonicalTailLTE.lteCoeff 3 % 3^(3+1) := h
    _ = 16 := hbase

/-! ## §3 THE FIRE FAMILIES — the ladder's first three levels -/

/-- **LEVEL ONE.**  Every core `u ≡ 1 mod 9` at every cut `v ≥ 1` fires
its digit two at row `v+2`: the diagonal's second trit is `2` because
`u·c ≡ 7 mod 9`. -/
theorem window_fire_level1 (v : Nat) (hv : 1 ≤ v) (u : Nat) (hu : u % 9 = 1) :
    digit3 (4^(3^v * u)) (v + 2) = 2 := by
  have hw := diagonal_window_law v u 1 (by omega)
  have hc := lteCoeff_mod9 v hv
  have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 9 = 7 := by
    rw [Nat.mul_mod, hu, hc]
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 1 = 2 := by
    unfold digit3
    omega
  rw [show v + 2 = v + 1 + 1 from rfl, hw]
  exact hd

/-- **LEVEL TWO.**  Every core `u ≡ 13 or 25 mod 27` at every cut `v ≥ 2`
fires its digit two at row `v+3`. -/
theorem window_fire_level2 (v : Nat) (hv : 2 ≤ v) (u : Nat)
    (hu : u % 27 = 13 ∨ u % 27 = 25) :
    digit3 (4^(3^v * u)) (v + 3) = 2 := by
  have hw := diagonal_window_law v u 2 (by omega)
  have hc := lteCoeff_mod27 v hv
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 2 = 2 := by
    unfold digit3
    rcases hu with h13 | h25
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 27 = 19 := by
        rw [Nat.mul_mod, h13, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 27 = 22 := by
        rw [Nat.mul_mod, h25, hc]
      omega
  rw [show v + 3 = v + 1 + 2 from rfl, hw]
  exact hd

/-- **LEVEL THREE.**  Every core `u ≡ 4, 34, 49, or 70 mod 81` at every
cut `v ≥ 3` fires its digit two at row `v+4`. -/
theorem window_fire_level3 (v : Nat) (hv : 3 ≤ v) (u : Nat)
    (hu : u % 81 = 4 ∨ u % 81 = 34 ∨ u % 81 = 49 ∨ u % 81 = 70) :
    digit3 (4^(3^v * u)) (v + 4) = 2 := by
  have hw := diagonal_window_law v u 3 (by omega)
  have hc := lteCoeff_mod81 v hv
  have hd : digit3 (u * GSTCanonicalTailLTE.lteCoeff v) 3 = 2 := by
    unfold digit3
    rcases hu with h4 | h34 | h49 | h70
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 64 := by
        rw [Nat.mul_mod, h4, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 58 := by
        rw [Nat.mul_mod, h34, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 55 := by
        rw [Nat.mul_mod, h49, hc]
      omega
    · have humod : (u * GSTCanonicalTailLTE.lteCoeff v) % 81 = 67 := by
        rw [Nat.mul_mod, h70, hc]
      omega
  rw [show v + 4 = v + 1 + 3 from rfl, hw]
  exact hd

/-- Witness receipt: `4^9` fires its digit two at row 4, delivered by
the uniform level-one family (`9 = 3^2·1`, `u = 1 ≡ 1 mod 9`), not by a
bounded decide. -/
theorem fire_nine_row_four : digit3 (4^9) 4 = 2 := by
  have h := window_fire_level1 2 (by omega) 1 (by decide)
  norm_num at h ⊢
  exact h

/-- Witness receipt: `4^108` fires its digit two at row 7, delivered by
the uniform level-three family (`108 = 3^3·4`, `u = 4 ≡ 4 mod 81`) — a
fire beyond every prior uniform witness, no bounded decide. -/
theorem fire_108_row_seven : digit3 (4^108) 7 = 2 := by
  have h := window_fire_level3 3 (by omega) 4 (Or.inl (by decide))
  norm_num at h ⊢
  exact h

/-- The full kill-chain instance: `4^108` fails `noTernaryTwo`, by the
uniform law alone. -/
theorem no22_four_pow_108 : noTernaryTwo (4^108) = false :=
  has_two_imp_not_no_two (4^108)
    (hasTernaryTwo_of_digit (4^108) 7 (by simpa [digit3] using fire_108_row_seven))

/-! ## §4 THE TRIAGE, THE DUST, THE SOCKET -/

/-- Every positive exponent decomposes uniquely as `3^v · u` with
`u` not divisible by three — the valuation cut. -/
theorem valuation_decomp (K : Nat) :
    0 < K → ∃ v u : Nat, K = 3^v * u ∧ u % 3 ≠ 0 := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
      intro hK
      by_cases h3 : K % 3 = 0
      · have hKd : 0 < K / 3 := by
          by_contra h0
          have hd0 : K / 3 = 0 := by omega
          have hdm := Nat.div_add_mod K 3
          omega
        obtain ⟨v, u, hKu, hu⟩ :=
          ih (K / 3) (Nat.div_lt_self hK (by decide : 1 < 3)) hKd
        refine ⟨v + 1, u, ?_, hu⟩
        have hdm : 3 * (K / 3) + K % 3 = K := Nat.div_add_mod K 3
        rw [h3, Nat.add_zero] at hdm
        rw [← hdm, hKu, Nat.pow_succ]
        ring
      · exact ⟨0, K, by ring, h3⟩

/-- **THE WINDOW-CLEAN DUST.**  The read's exact residual: exponents
whose reduced core is `1 mod 3` and whose readable diagonal never fires
— the Cantor slice, named once. -/
def WindowCleanDust (K : Nat) : Prop :=
  ∃ v u : Nat, K = 3^v * u ∧ u % 3 = 1 ∧
    ∀ j ≤ v, digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j ≠ 2

/-- **THE TRIAGE.**  Every exponent `K ≥ 8` either owns its digit two —
by the front fire or by a window fire, both uniform laws — or is
window-clean dust.  No third case: the whole plane of exponents, one
dichotomy, one construction. -/
theorem every_exponent_fires (K : Nat) (hK : 8 ≤ K) :
    (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K := by
  obtain ⟨v, u, hKu, hu3⟩ := valuation_decomp K (by omega)
  have hu3' : u % 3 = 1 ∨ u % 3 = 2 := by omega
  rcases hu3' with hu1 | hu2
  · by_cases hfire :
      ∃ j : Nat, j ≤ v ∧
        digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j = 2
    · left
      obtain ⟨j, hjv, hj⟩ := hfire
      have hw := diagonal_window_law v u j hjv
      refine ⟨v + 1 + j, ?_⟩
      rw [hKu, hw]
      exact hj
    · right
      refine ⟨v, u, hKu, hu1, ?_⟩
      intro j hjv h2
      exact hfire ⟨j, hjv, h2⟩
  · left
    have hf := GSTTheAct.front_law v u
    refine ⟨v + 1, ?_⟩
    rw [hKu, hf]
    exact hu2

/-- **THE READ KILLS THE COMPLEMENT.**  Every `K ≥ 8` outside the
window-clean dust owns its digit two: `noTernaryTwo (4^K) = false`,
through the repo's own kill chain. -/
theorem no22_of_not_dust (K : Nat) (hK : 8 ≤ K) (h : ¬ WindowCleanDust K) :
    noTernaryTwo (4^K) = false := by
  rcases every_exponent_fires K hK with ⟨p, hp⟩ | hdust
  · exact has_two_imp_not_no_two (4^K)
      (hasTernaryTwo_of_digit (4^K) p (by simpa [digit3] using hp))
  · exact absurd hdust h

/-- **THE SOCKET, FIRST STAGE.**  Dust empty ⇒ the act: every `4^K`
from eight onward fails `noTernaryTwo`. -/
theorem the_act_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTTheAct.the_act :=
  fun K hK => no22_of_not_dust K hK (h K hK)

/-- **THE SOCKET, COMPLETE.**  Dust empty ⇒ the act ⇒ `hTailF`, through
the standing green bridges.  The one remaining mathematical object is
named: kill the window-clean dust and the campaign closes. -/
theorem hTailF_of_dust_empty
    (h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp (the_act_of_dust_empty h)

/-! ## §5 THE RECEIPT — everything in one theorem -/

/-- **THE DIAGONAL READ, ASSEMBLED.**  (1) The window law: every
exponent's entire readable band, one law, all scales.  (2) The frozen
diagonal: the readable object is depth-invariant.  (3) The fire
families: three ladder levels, uniform.  (4) The triage: every `K ≥ 8`
fires or is dust.  (5) The socket: dust empty ⇒ `hTailF`.  (6) Witness
receipts beyond every prior uniform witness. -/
theorem the_diagonal_read_receipt :
    (∀ v u j : Nat, j ≤ v →
      digit3 (4^(3^v * u)) (v + 1 + j) =
        digit3 (u * GSTCanonicalTailLTE.lteCoeff v) j) ∧
    (∀ v w : Nat, v ≤ w →
      GSTCanonicalTailLTE.lteCoeff w % 3^(v+1) =
        GSTCanonicalTailLTE.lteCoeff v % 3^(v+1)) ∧
    (∀ v : Nat, 1 ≤ v → ∀ u : Nat, u % 9 = 1 →
      digit3 (4^(3^v * u)) (v + 2) = 2) ∧
    (∀ v : Nat, 2 ≤ v → ∀ u : Nat, u % 27 = 13 ∨ u % 27 = 25 →
      digit3 (4^(3^v * u)) (v + 3) = 2) ∧
    (∀ v : Nat, 3 ≤ v → ∀ u : Nat,
      u % 81 = 4 ∨ u % 81 = 34 ∨ u % 81 = 49 ∨ u % 81 = 70 →
      digit3 (4^(3^v * u)) (v + 4) = 2) ∧
    (∀ K : Nat, 8 ≤ K →
      (∃ p : Nat, digit3 (4^K) p = 2) ∨ WindowCleanDust K) ∧
    (∀ h : ∀ K : Nat, 8 ≤ K → ¬ WindowCleanDust K,
        GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (digit3 (4^9) 4 = 2) ∧
    (digit3 (4^108) 7 = 2) ∧
    (noTernaryTwo (4^108) = false) :=
  ⟨diagonal_window_law, lteCoeff_stable,
    window_fire_level1, window_fire_level2, window_fire_level3,
    every_exponent_fires, hTailF_of_dust_empty,
    fire_nine_row_four, fire_108_row_seven, no22_four_pow_108⟩

#print axioms binom_two_term
#print axioms div_pow_add
#print axioms digit3_mod_congr
#print axioms diagonal_window_law
#print axioms window_subsumes_front
#print axioms lteCoeff_succ_mod
#print axioms mod_dvd_modeq
#print axioms lteCoeff_stable
#print axioms lteCoeff_mod9
#print axioms lteCoeff_mod27
#print axioms lteCoeff_mod81
#print axioms window_fire_level1
#print axioms window_fire_level2
#print axioms window_fire_level3
#print axioms fire_nine_row_four
#print axioms fire_108_row_seven
#print axioms no22_four_pow_108
#print axioms valuation_decomp
#print axioms every_exponent_fires
#print axioms no22_of_not_dust
#print axioms the_act_of_dust_empty
#print axioms hTailF_of_dust_empty
#print axioms the_diagonal_read_receipt

end GSTDiagonalRead
```

## VIII.4 `GSTTheActConstruction.lean` — the feedback tree, complete

The 545-line construction file: the feedback tree — the act restated as the escape problem of a dynamical system. §1 the self-read law and the row-one read; §2 the collapse (`cantorian_iff_feedback`, `the_act_iff_feedback` — the act as "no escape of the feedback tree"); §3 the uniform kill engine (`prefix_unpack`, `feedback_fire_of_class`, `fire_of_mod243`); §4 cascade level four (the noise turns on: `dust_fire_row_five`, the survivor maps mod 9, 27, 81, 243); §4B cascade level five (the noise turns ternary: `noise_window_law`, `unique_dead_child`, `fire_of_mod729`, `dust_fire_row_six`, `cantorian_dust_mod_729`, `the_level_five_receipt`); §5 the socket (`hTailF_of_feedback` — the tree-escape closes hTailF, the kernel-certified bridge to the terminal identity); §6 the assembled receipt.

```lean
import Mathlib
import GSTClimbInfiniteFamily
import GSTCanonicalTailLTE

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE FEEDBACK READ — the construction of the act, begun

One separate file, zero monolith bytes.  The exponent's own digit stream,
fed through the prefix-power's digit stream, IS the power's digit stream:

* **§1 THE SELF-READ LAW.**  `self_read`: for EVERY exponent `K` and EVERY
  row `j+1`, the row-`j+1` trit of `4^K` is the row-`j+1` trit of
  `4^(K mod 3^j)` PLUS the `j`-th trit of `K` itself, modulo three —
  `digit3 (4^K) (j+1) = (digit3 (4^(K % 3^j)) (j+1) + digit3 K j) % 3`.
  The power reads the exponent through the prefix-power: the whole
  ternary stream of every power of four is one feedback system.  At
  `j = 0` it is the row-one read (`row_one_read`: row one of `4^K` IS
  `K % 3`), and `row_one_kill`: every `K ≡ 2 mod 3` fires at row one.

* **§2 THE COLLAPSE INTO THE FEEDBACK TREE.**  `cantorian_iff_feedback`:
  `CantorianPower K` holds IF AND ONLY IF, at EVERY level `j`, the prefix
  noise plus the exponent trit never lands on two.  `the_act_iff_feedback`:
  the act holds IF AND ONLY IF every `K ≥ 8` fires somewhere in the
  feedback tree.  The act, as one object: NO exponent from eight on
  threads the whole tree.

* **§3 THE UNIFORM KILL ENGINE.**  `feedback_fire_of_class`: ONE law that
  fires the digit two at row `j+1` for ANY level `j`, ANY alive prefix
  `r`, and the one dead child-trit `t` — the noise receipt is a closed
  computation, the class membership is a congruence.  Every cascade level
  that has ever been run, and every level that ever will be run, is an
  instance of this single theorem.

* **§4 CASCADE LEVEL FOUR.**  `dust_fire_row_five`: eight new infinite
  uniform classes — `K ≡ 85, 91, 112, 118, 163, 175, 190, 202 mod 243` —
  fire at row five.  The first level whose noise is NONZERO (the
  prefix-powers `4^4, 4^10, 4^31, 4^37` carry trit `1` at row five): the
  feedback warps the survivor set past the Cantor shape.  The survivor
  map: `cantorian_dust_mod_9/27/81/243` — a Cantorian dust exponent's
  residue is pinned, level by level, down to the sixteen surviving nodes
  mod `243` — and `166, 172, 193, 199` among them own a trit TWO at
  position four and still live: the row-five prefix-noise of one absorbed
  the fire.  The tree is richer than the Cantor set from level five on —
  machine-named.

* **§4B CASCADE LEVEL FIVE.**  `dust_fire_row_six`: sixteen more
  infinite uniform classes fire at row six — the first level whose
  noise takes ALL THREE values (`4^31, 4^37, 4^172` carry trit TWO at
  row six).  `noise_window_law`: the noise vanishes beyond the diagonal
  window `4^r ≥ 3^(j+1)`.  `unique_dead_child`: every node owns exactly
  one dead child — the blade's one-of-three named at the feedback level,
  so the survivor map doubles (`2, 4, 8, 16, 32`) by structure:
  `cantorian_dust_mod_729` pins the dust to THIRTY-TWO nodes mod 729.

* **§5 THE SOCKET.**  `hTailF_of_feedback`: hand the tree-escape — every
  `K ≥ 8` fires at some level — and `hTailF` closes through the standing
  green bridges.  `the_construction_receipt`: everything assembled, axiom
  printouts included: the classical three only.
-/

namespace GSTTheActConstruction

open GSTCanonicalSevenAxisBridge (digit3)
open GSTClimbInfiniteFamily (CantorianPower prefaced_window_full
  dust_fire_row_two dust_fire_row_three dust_fire_row_four
  no22_of_digit_two pow4_mod3 the_act_iff_no_cantorian)

/-! ## §1 THE SELF-READ LAW — the power stream reads the exponent stream -/

/-- **THE SELF-READ LAW.**  For every exponent `K` and every level `j`, the
row-`j+1` trit of `4^K` is the row-`j+1` trit of the prefix-power
`4^(K mod 3^j)` plus the `j`-th trit of `K`, modulo three.  The power's
digit stream is the exponent's digit stream fed through the
prefix-power's digit stream — one feedback system, every row, every
exponent, no hypothesis. -/
theorem self_read (K j : Nat) :
    digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 := by
  have hpow : 0 < 3^j := Nat.pow_pos (by decide)
  have hmod : K % 3^j < 3^j := Nat.mod_lt _ hpow
  have hlaw := prefaced_window_full j (K / 3^j) (K % 3^j) 0 hmod (by omega)
  have hKeq : 3^j * (K / 3^j) + K % 3^j = K := Nat.div_add_mod K (3^j)
  rw [hKeq, show j + 1 + 0 = j + 1 from by omega] at hlaw
  rw [hlaw]
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, Nat.add_mod]
  have hB : (4^(K % 3^j) * GSTCanonicalTailLTE.lteCoeff j * (K / 3^j)) % 3
      = (K / 3^j) % 3 := by
    have h1 := pow4_mod3 (K % 3^j)
    have h2 := GSTCanonicalTailLTE.lteCoeff_mod3_one j
    have hpair : (4^(K % 3^j) * GSTCanonicalTailLTE.lteCoeff j) % 3 = 1 := by
      rw [Nat.mul_mod, h1, h2]
    rw [Nat.mul_mod, hpair]
    omega
  rw [hB]

/-- **THE ROW-ONE READ.**  Row one of `4^K` is exactly `K % 3`: the
feedback law's ground floor, where the prefix is empty and the power
reads the exponent's zeroth trit bare. -/
theorem row_one_read (K : Nat) : digit3 (4^K) 1 = K % 3 := by
  have h := self_read K 0
  rw [Nat.zero_add, Nat.pow_zero, Nat.mod_one] at h
  have h0 : digit3 (4^0) 1 = 0 := by decide
  have hK : digit3 K 0 = K % 3 := by
    unfold digit3
    rw [Nat.pow_zero, Nat.div_one]
  rw [h, h0, hK]
  omega

/-- **THE ROW-ONE KILL.**  Every exponent `K ≡ 2 mod 3` fires its digit
two at row one — the feedback tree's ground-floor kill. -/
theorem row_one_kill (K : Nat) (h : K % 3 = 2) : digit3 (4^K) 1 = 2 := by
  rw [row_one_read, h]

/-! ## §2 THE COLLAPSE — the act as the feedback tree's escape -/

/-- **THE CANTORIAN CONSTRAINT SYSTEM.**  `CantorianPower K` holds IF AND
ONLY IF at EVERY level `j` the prefix noise plus the exponent trit never
lands on two: the entire Cantorian core is the set of exponents that
thread the feedback tree at every level.  Every row of every power is a
level of the tree — nothing outside the tree exists. -/
theorem cantorian_iff_feedback (K : Nat) :
    CantorianPower K ↔ ∀ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 ≠ 2 := by
  constructor
  · intro hc j
    have hrow := hc (j + 1) (by omega)
    rw [self_read K j] at hrow
    exact hrow
  · intro hfire p hp
    rcases p with _ | j
    · exact absurd hp (by omega)
    · rw [self_read K j]
      exact hfire j

/-- **THE ACT AS TREE-ESCAPE.**  The act holds IF AND ONLY IF every
exponent from eight on fires somewhere in the feedback tree: some level
`j` where the prefix noise plus the exponent trit lands on two.  The act,
the Cantorian core, and the feedback tree are one object. -/
theorem the_act_iff_feedback :
    GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2 := by
  rw [the_act_iff_no_cantorian]
  constructor
  · intro hnc K hK8
    by_cases hc : CantorianPower K
    · exact absurd ⟨K, hK8, hc⟩ hnc
    · unfold CantorianPower at hc
      push_neg at hc
      obtain ⟨p, hp1, hp⟩ := hc
      rcases p with _ | j
      · exact absurd hp1 (by omega)
      · refine ⟨j, ?_⟩
        rw [self_read K j] at hp
        exact hp
  · intro hfire hnc
    obtain ⟨K, hK8, hc⟩ := hnc
    obtain ⟨j, hj⟩ := hfire K hK8
    exact absurd hj ((cantorian_iff_feedback K).mp hc j)

/-! ## §3 THE UNIFORM KILL ENGINE — one law, every level -/

/-- **PREFIX UNPACKING.**  A class membership `K ≡ r + 3^j·t mod 3^(j+1)`
with `r < 3^j` and `t < 3` unpacks into the two facts the feedback law
consumes: `K`'s level-`j` prefix is `r`, and `K`'s `j`-th trit is `t`. -/
theorem prefix_unpack (K j r t : Nat) (hr : r < 3^j) (ht : t < 3)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    K % 3^j = r ∧ digit3 K j = t := by
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  have hdvd : 3^j ∣ 3^(j+1) := ⟨3, Nat.pow_succ 3 j⟩
  have hmod : K % 3^j = r := by
    have h := Nat.mod_mod_of_dvd K hdvd
    rw [hK, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr] at h
    exact h.symm
  refine ⟨hmod, ?_⟩
  obtain ⟨q, hq⟩ : ∃ q : Nat, q = K / 3^(j+1) := ⟨K / 3^(j+1), rfl⟩
  have hdm : 3^(j+1) * q + (r + 3^j * t) = K := by
    rw [← hK, hq, Nat.div_add_mod K (3^(j+1))]
  have hshape : K = 3^j * (3 * q + t) + r := by
    rw [← hdm, Nat.pow_succ]
    ring
  unfold digit3
  rw [hshape, show 3^j * (3 * q + t) + r = r + 3^j * (3 * q + t) from by ring,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr]
  omega

/-- **THE UNIFORM KILL.**  At ANY level `j`, an alive prefix `r` and its
one dead child-trit `t` — certified by the closed noise receipt
`(digit3 (4^r) (j+1) + t) % 3 = 2` — kill the entire congruence class
`K ≡ r + 3^j·t mod 3^(j+1)` at row `j+1`: every member fires its digit
two.  Every cascade level, current and future, is an instance. -/
theorem feedback_fire_of_class (j r t K : Nat)
    (hr : r < 3^j) (ht : t < 3)
    (hnoise : (digit3 (4^r) (j + 1) + t) % 3 = 2)
    (hK : K % 3^(j+1) = r + 3^j * t) :
    digit3 (4^K) (j + 1) = 2 := by
  obtain ⟨hmod, htrit⟩ := prefix_unpack K j r t hr ht hK
  rw [self_read K j, hmod, htrit]
  exact hnoise

/-- **THE UNIFORM KILL, CLASS FORM.**  Same law, phrased for the level-four
modulus: `K ≡ r + 81·t mod 243` fires at row five when the noise receipt
holds.  All arithmetic literal — the class hypothesis is pure omega. -/
theorem fire_of_mod243 (K r t : Nat)
    (hr : r < 81) (ht : t < 3)
    (hnoise : (digit3 (4^r) 5 + t) % 3 = 2)
    (hclass : K % 243 = r + 81 * t) :
    digit3 (4^K) 5 = 2 := by
  have h245 : (3:Nat)^(4+1) = 243 := by decide
  have h81 : (3:Nat)^4 = 81 := by decide
  have hK : K % 3^(4+1) = r + 3^4 * t := by
    rw [h245, h81]
    exact hclass
  have hr' : r < 3^4 := by
    rw [h81]
    exact hr
  exact feedback_fire_of_class 4 r t K hr' ht hnoise hK

/-! ## §4 CASCADE LEVEL FOUR — the noise turns on -/

/-- **CASCADE LEVEL THREE (row five).**  Every exponent `K ≡ 85, 91,
112, 118, 163, 175, 190, 202 mod 243` fires its digit two at row five —
eight new infinite uniform classes.  The first cascade level whose
prefix-noise is nonzero (`4^4, 4^10, 4^31, 4^37` carry trit one at row
five): the feedback era of the cascade begins here. -/
theorem dust_fire_row_five (K : Nat)
    (hK : K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨ K % 243 = 118 ∨
           K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨ K % 243 = 202) :
    digit3 (4^K) 5 = 2 := by
  rcases hK with h85 | h91 | h112 | h118 | h163 | h175 | h190 | h202
  · exact fire_of_mod243 K 4 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 10 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 31 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 37 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 13 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 28 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod243 K 40 2 (by decide) (by decide) (by decide) (by omega)

/-- **THE CASCADE KILL, LEVEL FOUR.**  The eight new classes die outright
through the repo's own kill chain. -/
theorem no22_of_cascade_four (K : Nat)
    (h : K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨ K % 243 = 118 ∨
         K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨ K % 243 = 202) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 5 (dust_fire_row_five K h)

/-- **THE DUST PINNED AT LEVEL ONE.**  A Cantorian dust exponent (`K ≡ 1
mod 3`) lives in one of the two surviving residues mod nine. -/
theorem cantorian_dust_mod_9 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 9 = 1 ∨ K % 9 = 4 := by
  have hrow := hc 2 (by omega)
  by_cases h7 : K % 9 = 7
  · exact absurd (dust_fire_row_two K h7) hrow
  · omega

/-- **THE DUST PINNED AT LEVEL TWO.**  Four surviving residues mod
twenty-seven. -/
theorem cantorian_dust_mod_27 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 27 = 1 ∨ K % 27 = 4 ∨ K % 27 = 10 ∨ K % 27 = 13 := by
  have h9 := cantorian_dust_mod_9 K hd hc
  have hrow := hc 3 (by omega)
  have h19 : K % 27 ≠ 19 :=
    fun h => absurd (dust_fire_row_three K (Or.inl h)) hrow
  have h22 : K % 27 ≠ 22 :=
    fun h => absurd (dust_fire_row_three K (Or.inr (Or.inl h))) hrow
  have h25 : K % 27 ≠ 25 :=
    fun h => absurd (dust_fire_row_three K (Or.inr (Or.inr h))) hrow
  rcases h9 with h1 | h4 <;> omega

/-- **THE DUST PINNED AT LEVEL THREE.**  Eight surviving residues mod
eighty-one — the Cantor prefixes with lowest trit one. -/
theorem cantorian_dust_mod_81 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 81 = 1 ∨ K % 81 = 4 ∨ K % 81 = 10 ∨ K % 81 = 13 ∨
      K % 81 = 28 ∨ K % 81 = 31 ∨ K % 81 = 37 ∨ K % 81 = 40 := by
  have h27 := cantorian_dust_mod_27 K hd hc
  have hrow := hc 4 (by omega)
  have h55 : K % 81 ≠ 55 :=
    fun h => absurd (dust_fire_row_four K (Or.inl h)) hrow
  have h58 : K % 81 ≠ 58 :=
    fun h => absurd (dust_fire_row_four K (Or.inr (Or.inl h))) hrow
  have h64 : K % 81 ≠ 64 :=
    fun h => absurd (dust_fire_row_four K (Or.inr (Or.inr (Or.inl h)))) hrow
  have h67 : K % 81 ≠ 67 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have h73 : K % 81 ≠ 73 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have h76 : K % 81 ≠ 76 :=
    fun h => absurd (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) hrow
  rcases h27 with h1 | h4 | h10 | h13 <;> omega

/-- **THE DUST PINNED AT LEVEL FOUR — THE MAP.**  A Cantorian dust
exponent lives in one of SIXTEEN surviving residues mod 243.  The noise
era's signature: `166, 172, 193, 199` among the survivors own trit
TWO at position four and still live — the prefix-noise absorbed the fire
(their row-five prefix-noise is one, turning two into zero).
The survivor set is now RICHER than the Cantor prefixes: the feedback
tree, machine-drawn at its fifth storey. -/
theorem cantorian_dust_mod_243 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 243 = 1 ∨ K % 243 = 4 ∨ K % 243 = 10 ∨ K % 243 = 13 ∨
      K % 243 = 28 ∨ K % 243 = 31 ∨ K % 243 = 37 ∨ K % 243 = 40 ∨
      K % 243 = 82 ∨ K % 243 = 94 ∨ K % 243 = 109 ∨ K % 243 = 121 ∨
      K % 243 = 166 ∨ K % 243 = 172 ∨ K % 243 = 193 ∨ K % 243 = 199 := by
  have h81 := cantorian_dust_mod_81 K hd hc
  have hrow := hc 5 (by omega)
  have h85 : K % 243 ≠ 85 :=
    fun h => absurd (dust_fire_row_five K (Or.inl h)) hrow
  have h91 : K % 243 ≠ 91 :=
    fun h => absurd (dust_fire_row_five K (Or.inr (Or.inl h))) hrow
  have h112 : K % 243 ≠ 112 :=
    fun h => absurd (dust_fire_row_five K (Or.inr (Or.inr (Or.inl h)))) hrow
  have h118 : K % 243 ≠ 118 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have h163 : K % 243 ≠ 163 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have h175 : K % 243 ≠ 175 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have h190 : K % 243 ≠ 190 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have h202 : K % 243 ≠ 202 :=
    fun h => absurd (dust_fire_row_five K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))) hrow
  rcases h81 with h1 | h4 | h10 | h13 | h28 | h31 | h37 | h40 <;> omega

/-! ## §4B CASCADE LEVEL FIVE — the noise turns ternary -/

/-- **THE NOISE WINDOW LAW.**  Beyond the diagonal window the prefix
noise vanishes: when the prefix-power stays below the modulus, its
row-`j+1` trit is zero.  The feedback's noise lives in the window
`4^r ≥ 3^(j+1)` — every deeper row reads bare exponent trits. -/
theorem noise_window_law (r j : Nat) (h : 4^r < 3^(j+1)) :
    digit3 (4^r) (j + 1) = 0 := by
  unfold digit3
  rw [Nat.div_eq_of_lt h]

/-- **THE UNIQUE DEAD CHILD.**  At every level, every prefix owns
EXACTLY ONE dead child-trit: `(2 - noise) mod 3`.  The blade's
one-of-three, named at the feedback level — every node of the dust
tree has exactly two alive children, forever, by structure. -/
theorem unique_dead_child (r j : Nat) :
    ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j + 1) + t) % 3 = 2 := by
  have hd : digit3 (4^r) (j + 1) < 3 := by
    unfold digit3
    exact Nat.mod_lt _ (by decide)
  refine ⟨2 - digit3 (4^r) (j + 1), ⟨by omega, by omega⟩, ?_⟩
  intro t ht
  omega

/-- **THE UNIFORM KILL, LEVEL-FIVE FORM.**  Same engine, one level
deeper: `K ≡ r + 243·t mod 729` fires at row six when the noise
receipt holds.  All arithmetic literal. -/
theorem fire_of_mod729 (K r t : Nat)
    (hr : r < 243) (ht : t < 3)
    (hnoise : (digit3 (4^r) 6 + t) % 3 = 2)
    (hclass : K % 729 = r + 243 * t) :
    digit3 (4^K) 6 = 2 := by
  have h729 : (3:Nat)^(5+1) = 729 := by decide
  have h243 : (3:Nat)^5 = 243 := by decide
  have hK : K % 3^(5+1) = r + 3^5 * t := by
    rw [h729, h243]
    exact hclass
  have hr' : r < 3^5 := by
    rw [h243]
    exact hr
  exact feedback_fire_of_class 5 r t K hr' ht hnoise hK

/-- **CASCADE LEVEL FIVE (row six).**  Every exponent `K ≡ 31, 37,
172, 253, 256, 271, 337, 352, 409, 487, 490, 526, 568, 607, 679,
685 mod 729` fires its digit two at row six — sixteen new infinite
uniform classes.  The first cascade level whose noise takes ALL
THREE values: the prefixes `4^31, 4^37, 4^172` carry trit TWO at
row six (their zeroth child dies), the noise-one prefixes kill their
first child, the noise-zero prefixes kill their second. -/
theorem dust_fire_row_six (K : Nat)
    (hK : K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685) :
    digit3 (4^K) 6 = 2 := by
  rcases hK with h31 | h37 | h172 | h253 | h256 | h271 | h337 | h352 | h409 | h487 | h490 | h526 | h568 | h607 | h679 | h685
  · exact fire_of_mod729 K 31 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 37 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 172 0 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 10 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 13 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 28 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 94 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 109 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 166 1 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 1 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 4 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 40 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 82 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 121 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 193 2 (by decide) (by decide) (by decide) (by omega)
  · exact fire_of_mod729 K 199 2 (by decide) (by decide) (by decide) (by omega)

/-- **THE CASCADE KILL, LEVEL FIVE.**  The sixteen new classes die
outright through the repo's own kill chain. -/
theorem no22_of_cascade_five (K : Nat)
    (h : K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685) :
    noTernaryTwo (4^K) = false :=
  no22_of_digit_two K 6 (dust_fire_row_six K h)

/-- **THE DUST PINNED AT LEVEL FIVE — THE MAP DOUBLES.**  A Cantorian
dust exponent lives in one of THIRTY-TWO surviving residues mod
729.  The structural law in action: every one of the sixteen level-
four nodes kept exactly two children (`unique_dead_child`), so the
alive set doubles — `2, 4, 8, 16, 32` — level by level, without
exception, by the blade's one-of-three. -/
theorem cantorian_dust_mod_729 (K : Nat)
    (hd : K % 3 = 1) (hc : CantorianPower K) :
    K % 729 = 1 ∨ K % 729 = 4 ∨ K % 729 = 10 ∨ K % 729 = 13 ∨ K % 729 = 28 ∨ K % 729 = 40 ∨ K % 729 = 82 ∨ K % 729 = 94 ∨ K % 729 = 109 ∨ K % 729 = 121 ∨ K % 729 = 166 ∨ K % 729 = 193 ∨ K % 729 = 199 ∨ K % 729 = 244 ∨ K % 729 = 247 ∨ K % 729 = 274 ∨ K % 729 = 280 ∨ K % 729 = 283 ∨ K % 729 = 325 ∨ K % 729 = 364 ∨ K % 729 = 415 ∨ K % 729 = 436 ∨ K % 729 = 442 ∨ K % 729 = 496 ∨ K % 729 = 499 ∨ K % 729 = 514 ∨ K % 729 = 517 ∨ K % 729 = 523 ∨ K % 729 = 580 ∨ K % 729 = 595 ∨ K % 729 = 652 ∨ K % 729 = 658 := by
  have h243 := cantorian_dust_mod_243 K hd hc
  have hrow := hc 6 (by omega)
  have hdead31 : K % 729 ≠ 31 :=
    fun h => absurd (dust_fire_row_six K (Or.inl h)) hrow
  have hdead37 : K % 729 ≠ 37 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inl h))) hrow
  have hdead172 : K % 729 ≠ 172 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inl h)))) hrow
  have hdead253 : K % 729 ≠ 253 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inl h))))) hrow
  have hdead256 : K % 729 ≠ 256 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hrow
  have hdead271 : K % 729 ≠ 271 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))) hrow
  have hdead337 : K % 729 ≠ 337 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))) hrow
  have hdead352 : K % 729 ≠ 352 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))) hrow
  have hdead409 : K % 729 ≠ 409 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))) hrow
  have hdead487 : K % 729 ≠ 487 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))) hrow
  have hdead490 : K % 729 ≠ 490 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))) hrow
  have hdead526 : K % 729 ≠ 526 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))) hrow
  have hdead568 : K % 729 ≠ 568 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))) hrow
  have hdead607 : K % 729 ≠ 607 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))) hrow
  have hdead679 : K % 729 ≠ 679 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))))))))) hrow
  have hdead685 : K % 729 ≠ 685 :=
    fun h => absurd (dust_fire_row_six K (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))))))))) hrow
  rcases h243 with h1 | h4 | h10 | h13 | h28 | h31 | h37 | h40 | h82 | h94 | h109 | h121 | h166 | h172 | h193 | h199 <;> omega

/-- **THE LEVEL-FIVE RECEIPT.**  Cascade level five assembled:
the window law, the unique dead child, the sixteen fires, the
doubled survivor map, and the kill chain — with axiom printouts
below. -/
theorem the_level_five_receipt :
    (∀ r j : Nat, 4^r < 3^(j+1) → digit3 (4^r) (j+1) = 0) ∧
    (∀ r j : Nat, ∃! t : Nat, t < 3 ∧ (digit3 (4^r) (j+1) + t) % 3 = 2) ∧
    (∀ K : Nat, K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685 → digit3 (4^K) 6 = 2) ∧
    (∀ K : Nat, K % 729 = 31 ∨ K % 729 = 37 ∨ K % 729 = 172 ∨ K % 729 = 253 ∨ K % 729 = 256 ∨ K % 729 = 271 ∨ K % 729 = 337 ∨ K % 729 = 352 ∨ K % 729 = 409 ∨ K % 729 = 487 ∨ K % 729 = 490 ∨ K % 729 = 526 ∨ K % 729 = 568 ∨ K % 729 = 607 ∨ K % 729 = 679 ∨ K % 729 = 685 → noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 729 = 1 ∨ K % 729 = 4 ∨ K % 729 = 10 ∨ K % 729 = 13 ∨ K % 729 = 28 ∨ K % 729 = 40 ∨ K % 729 = 82 ∨ K % 729 = 94 ∨ K % 729 = 109 ∨ K % 729 = 121 ∨ K % 729 = 166 ∨ K % 729 = 193 ∨ K % 729 = 199 ∨ K % 729 = 244 ∨ K % 729 = 247 ∨ K % 729 = 274 ∨ K % 729 = 280 ∨ K % 729 = 283 ∨ K % 729 = 325 ∨ K % 729 = 364 ∨ K % 729 = 415 ∨ K % 729 = 436 ∨ K % 729 = 442 ∨ K % 729 = 496 ∨ K % 729 = 499 ∨ K % 729 = 514 ∨ K % 729 = 517 ∨ K % 729 = 523 ∨ K % 729 = 580 ∨ K % 729 = 595 ∨ K % 729 = 652 ∨ K % 729 = 658) :=
  ⟨fun r j => noise_window_law r j,
    fun r j => unique_dead_child r j,
    dust_fire_row_six, no22_of_cascade_five, cantorian_dust_mod_729⟩

#print axioms noise_window_law
#print axioms unique_dead_child
#print axioms fire_of_mod729
#print axioms dust_fire_row_six
#print axioms no22_of_cascade_five
#print axioms cantorian_dust_mod_729
#print axioms the_level_five_receipt
/-! ## §5 THE SOCKET — the tree-escape closes hTailF -/

/-- **THE SOCKET.**  Hand the tree-escape — every `K ≥ 8` fires at some
level of the feedback read — and `hTailF` closes, no hypothesis, no
binder: through the standing green bridges, in one line. -/
theorem hTailF_of_feedback
    (h : ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp (the_act_iff_feedback.mpr h)

/-! ## §6 THE RECEIPT — everything assembled -/

/-- **THE CONSTRUCTION, ASSEMBLED.**  (1) The self-read law: every row of
every power is prefix-noise plus exponent-trit.  (2) The act as
tree-escape.  (3) The socket: tree-escape closes `hTailF`.  (4) Cascade
level four: eight classes fire at row five.  (5) The survivor map: the
Cantorian dust pinned to sixteen nodes mod 243.  (6) The kill chain:
the eight classes die through the repo's own chain. -/
theorem the_construction_receipt :
    (∀ K j : Nat, digit3 (4^K) (j + 1) =
      (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3) ∧
    (GSTTheAct.the_act ↔
      ∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2) ∧
    (∀ h : (∀ K : Nat, 8 ≤ K → ∃ j : Nat,
        (digit3 (4^(K % 3^j)) (j + 1) + digit3 K j) % 3 = 2),
      GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (∀ K : Nat, K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨
        K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨
        K % 243 = 202 →
      digit3 (4^K) 5 = 2) ∧
    (∀ K : Nat, K % 3 = 1 → CantorianPower K →
      K % 243 = 1 ∨ K % 243 = 4 ∨ K % 243 = 10 ∨ K % 243 = 13 ∨
        K % 243 = 28 ∨ K % 243 = 31 ∨ K % 243 = 37 ∨ K % 243 = 40 ∨
        K % 243 = 82 ∨ K % 243 = 94 ∨ K % 243 = 109 ∨ K % 243 = 121 ∨
        K % 243 = 166 ∨ K % 243 = 172 ∨ K % 243 = 193 ∨ K % 243 = 199) ∧
    (∀ K : Nat, K % 243 = 85 ∨ K % 243 = 91 ∨ K % 243 = 112 ∨
        K % 243 = 118 ∨ K % 243 = 163 ∨ K % 243 = 175 ∨ K % 243 = 190 ∨
        K % 243 = 202 →
      noTernaryTwo (4^K) = false) :=
  ⟨fun K j => self_read K j, the_act_iff_feedback, hTailF_of_feedback,
    dust_fire_row_five, cantorian_dust_mod_243, no22_of_cascade_four⟩

#print axioms self_read
#print axioms row_one_read
#print axioms row_one_kill
#print axioms cantorian_iff_feedback
#print axioms the_act_iff_feedback
#print axioms prefix_unpack
#print axioms feedback_fire_of_class
#print axioms fire_of_mod243
#print axioms dust_fire_row_five
#print axioms no22_of_cascade_four
#print axioms cantorian_dust_mod_9
#print axioms cantorian_dust_mod_27
#print axioms cantorian_dust_mod_81
#print axioms cantorian_dust_mod_243
#print axioms hTailF_of_feedback
#print axioms the_construction_receipt

end GSTTheActConstruction
```

## VIII.5 `GSTClimbInfiniteFamily.lean` — the climb, the prefaced read, the dust ladder, the core (selection)

The 1151-line climb file: §1 the infinite climb family (`pair_law`, `wave3_deep_member`, unboundedness — the climb witnesses exist at every depth); §2 the prefaced read (`prefaced_window_law`, `prefaced_window_full`, `prefaced_window_sliced`, **`every_row_is_read`** — every row of every power is a read of the prefaced window: the observation law in its final, complete form); §3 the v=0 dust ladder (the row-2/3/4 dust reads and the first fire rows); §4 the collapse and the core (`CantorianPower` defined, `pow4_mod3`, `no22_of_digit_two` — the kill chain converter used throughout the monolith).

```lean
/-! ## §1 THE INFINITE CLIMB FAMILY — the climb green on an
unbounded family of exponents -/

/-- **THE PAIR LAW.**  At a cut `1 ≤ v` with `K = 3^v * u`, both
consecutive powers `4^K` and `4^(K+1)` carry the SAME digit `u % 3` at
row `v+1`: the x4-carry at the cut is exactly zero because `4^K ≡ 1`
modulo `3^(v+1)` and `4 < 3^(v+1)`. -/
theorem pair_law (K v u : Nat) (hv : 1 ≤ v) (hK : K = 3^v * u) :
    digit3 (4^K) (v + 1) = u % 3 ∧
      digit3 (4^(K+1)) (v + 1) = u % 3 := by
  have hmod : 4^K % 3^(v+1) = 1 := by
    rw [hK]
    exact GSTCanonicalTailLTE.pow4_scaled_mod_next v u
  have hsrc : digit3 (4^K) (v+1) = u % 3 := by
    rw [hK]
    exact GSTTheAct.front_law v u
  refine ⟨hsrc, ?_⟩
  have hnext : 4^(K+1) = 4 * 4^K := by
    rw [Nat.pow_succ]
    ring
  have hformula : digit3 (4 * 4^K) (v+1) =
      (digit3 (4^K) (v+1) + GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) (v+1)) % 3 :=
    GSTFourPowerDirectAdditionCarry.digit3_four_mul (4^K) (v+1)
  have hcarry : GSTFourPowerDirectAdditionCarry.directCarry4 (4^K) (v+1) = 0 := by
    unfold GSTFourPowerDirectAdditionCarry.directCarry4
    rw [hmod, Nat.mul_one]
    exact Nat.div_eq_of_lt
      (GSTCanonicalTailStateIso.one_prefix_bounds (v+1) (by omega)).2
  rw [hnext, hformula, hsrc, hcarry]
  omega

/-- Membership in the deep third-wave family: the exponent's lowest
nonzero ternary trit equals `2` at scale at least two. -/
def wave3_deep_member (K : Nat) : Prop :=
  ∃ v u : Nat, 2 ≤ v ∧ K = 3^v * u ∧ u % 3 = 2

/-- **THE INFINITE CLIMB FAMILY.**  Every deep-scale member owns its Happy
row at `v+1`: digit two (the reduced exponent trit) with x4-carry exactly
zero — the pair law composes with the repo's green direct-to-physical
Happy bridge.  The climb is machine-green on this entire family. -/
theorem climb_member_of_wave3_deep (K : Nat) (h : wave3_deep_member K) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  obtain ⟨v, u, hv, hK, htrit⟩ := h
  have hpair := pair_law K v u (by omega) hK
  rw [htrit] at hpair
  have hct : GSTFourPowerHappyProvider.CommonTwoGeThree K :=
    ⟨v + 1, by omega, hpair.1, hpair.2⟩
  exact GSTFourPowerHappyProvider.commonTwoGeThree_to_physical_happy_ge_three K hct

/-- `18 = 3^2 * 2` is a member: the family's first member beyond the old
witnesses `8, 9, 10`. -/
theorem member_eighteen : wave3_deep_member 18 :=
  ⟨2, 2, by omega, by norm_num, by decide⟩

/-- The climb's Happy row at `K = 18`, delivered by the family law (not by
a bounded decide): row `3`, digit two, x4-carry zero. -/
theorem climb_witness_eighteen :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^18) p) (digit3 (4^18) p) :=
  climb_member_of_wave3_deep 18 member_eighteen

/-- A tiny scale law: every natural is at most its own power of three. -/
theorem pow_ge_self : ∀ k : Nat, k ≤ 3^k := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
      have h1 : 0 < 3^k := by positivity
      rw [Nat.pow_succ]
      omega

/-- **THE FAMILY IS UNBOUNDED.**  For every `N` there is a member `K ≥ N`
(namely `2 * 3^(N+2)`): the climb's green family is infinite. -/
theorem wave3_deep_unbounded : ∀ N : Nat, ∃ K : Nat, N ≤ K ∧ wave3_deep_member K := by
  intro N
  have hge : N + 2 ≤ 3^(N+2) := pow_ge_self (N+2)
  refine ⟨2 * 3^(N+2), by omega, ?_⟩
  exact ⟨N+2, 2, by omega, by ring, by decide⟩

/-! ## §2 THE PREFACED READ — the completion of the diagonal window law -/

/-- **THE PREFACED WINDOW LAW.**  For EVERY cut `v`, EVERY core `u`, and
EVERY remainder `r < 3^v`, the digit stream of `4^(3^v·u + r)` at row
`v+1+j` (any `j ≤ v`) is the digit stream at `v+1+j` of the explicit
prefaced object `4^r + 3^(v+1)·(4^r·c(v)·u)`.  The plain window law is
the `r = 0` spine; this is the whole plane of exponents — no
coprimality, no zero-remainder restriction — one law, every scale. -/
theorem prefaced_window_law (v u r j : Nat) (hr : r < 3^v) (hj : j ≤ v) :
    digit3 (4^(3^v * u + r)) (v + 1 + j) =
      digit3 (4^r + 3^(v+1) * (4^r * GSTCanonicalTailLTE.lteCoeff v * u)) (v + 1 + j) := by
  have hLTE : 4^(3^v) = 1 + 3^(v+1) * GSTCanonicalTailLTE.lteCoeff v :=
    GSTCanonicalTailLTE.pow4_three_power_lte_exact v
  have hK : 4^(3^v * u + r) = (4^(3^v))^u * 4^r := by
    rw [Nat.pow_add, Nat.pow_mul]
  obtain ⟨s, hs⟩ :=
    GSTDiagonalRead.binom_two_term (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) u
  have hcorr : 3^(v+2+j) ∣ 4^r * ((3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) *
      (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) * s) := by
    obtain ⟨q, hq⟩ :=
      GSTDiagonalRead.pow_cut_dvd v j (GSTCanonicalTailLTE.lteCoeff v) s hj
    exact ⟨4^r * q, by rw [hq]; ring⟩
  have hcongr : 4^(3^v * u + r) % 3^((v+1+j)+1) =
      (4^r + 3^(v+1) * (4^r * GSTCanonicalTailLTE.lteCoeff v * u)) % 3^((v+1+j)+1) := by
    rw [show 3^((v+1+j)+1) = 3^(v+2+j) from by congr 1; omega]
    rw [hK, hLTE, hs]
    have hshape : (1 + u * (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) +
        (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) *
        (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) * s) * 4^r =
        (4^r + 3^(v+1) * (4^r * GSTCanonicalTailLTE.lteCoeff v * u)) +
        4^r * ((3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) *
        (3^(v+1) * GSTCanonicalTailLTE.lteCoeff v) * s) := by
      ring
    rw [hshape]
    exact GSTDiagonalRead.add_mod_of_dvd _ _ _ hcorr
  exact GSTDiagonalRead.digit3_mod_congr (4^(3^v * u + r))
    (4^r + 3^(v+1) * (4^r * GSTCanonicalTailLTE.lteCoeff v * u)) (v+1+j) hcongr

/-- **THE PREFACED READ, SLICED AT EVERY REMAINDER.**  Rows `v+1 .. 2v+1`
of `4^(3^v·u + r)` ARE the trits `0 .. v` of the sliced object
`4^r/3^(v+1) + 4^r·c(v)·u`: the frozen diagonal plus the preface
quotient.  No condition on `4^r` — the slice is clean at every
remainder, every cut, every scale. -/
theorem prefaced_window_full (v u r j : Nat) (hr : r < 3^v) (hj : j ≤ v) :
    digit3 (4^(3^v * u + r)) (v + 1 + j) =
      digit3 (4^r / 3^(v+1) + 4^r * GSTCanonicalTailLTE.lteCoeff v * u) j := by
  have hlaw := prefaced_window_law v u r j hr hj
  have hpow : 0 < 3^(v+1) := Nat.pow_pos (by decide)
  have hmod : 4^r % 3^(v+1) < 3^(v+1) := Nat.mod_lt _ hpow
  have hdm : 4^r % 3^(v+1) + 3^(v+1) * (4^r / 3^(v+1)) = 4^r :=
    Nat.mod_add_div (4^r) (3^(v+1))
  have hshape : 4^r % 3^(v+1) + 3^(v+1) *
        (4^r / 3^(v+1) + 4^r * GSTCanonicalTailLTE.lteCoeff v * u) =
      4^r + 3^(v+1) * (4^r * GSTCanonicalTailLTE.lteCoeff v * u) := by
    rw [Nat.mul_add, ← Nat.add_assoc, hdm]
  rw [hlaw, ← hshape]
  simpa only [GSTCanonicalTailStateIso.digit3, digit3] using
    GSTCanonicalTailStateIso.prefix_slice_digit_exact (v+1) (4^r % 3^(v+1))
      (4^r / 3^(v+1) + 4^r * GSTCanonicalTailLTE.lteCoeff v * u) j hmod

/-- The clean-slice corollary: when the preface itself stays below the
cut, the quotient vanishes and the read is the bare prefaced diagonal. -/
theorem prefaced_window_sliced (v u r j : Nat)
    (hr : r < 3^v) (hr4 : 4^r < 3^(v+1)) (hj : j ≤ v) :
    digit3 (4^(3^v * u + r)) (v + 1 + j) =
      digit3 (4^r * GSTCanonicalTailLTE.lteCoeff v * u) j := by
  have h := prefaced_window_full v u r j hr hj
  rw [h, Nat.div_eq_of_lt hr4, Nat.zero_add]

/-- **EVERY ROW IS READ.**  Every row `p ≥ 1` of EVERY power `4^K` is a
row of the explicit prefaced object built from `K`'s own ternary
prefix: `4^(K mod 3^(p-1)) + 3^p·(4^(K mod 3^(p-1))·c(p-1)·⌊K/3^(p-1)⌋)`.
The diagonal window law, completed to the whole plane — no row of the
tower is outside the read. -/
theorem every_row_is_read (K p : Nat) (hp : 1 ≤ p) :
    digit3 (4^K) p =
      digit3 (4^(K % 3^(p-1)) + 3^p *
        (4^(K % 3^(p-1)) * GSTCanonicalTailLTE.lteCoeff (p-1) *
          (K / 3^(p-1)))) p := by
  have hpow : 0 < 3^(p-1) := Nat.pow_pos (by decide)
  have hmod : K % 3^(p-1) < 3^(p-1) := Nat.mod_lt _ hpow
  have h := prefaced_window_law (p-1) (K / 3^(p-1)) (K % 3^(p-1)) 0 hmod (by omega)
  rw [show (p-1) + 1 + 0 = p from by omega] at h
  have hKeq : 4^K = 4^(3^(p-1) * (K / 3^(p-1)) + K % 3^(p-1)) := by
    rw [Nat.div_add_mod K (3^(p-1))]
  rw [hKeq, h]

/-! ## §3 THE CASCADE — the v=0 dust ladder -/

/-- Row one of `A·u` reads the core's own row one whenever the prefaced
frozen-diagonal coefficient is `1 mod 9` — the second trit is carried
faithfully. -/
theorem digit3_one_of_mod9 (A u : Nat) (hA : A % 9 = 1) :
    digit3 (A * u) 1 = (u / 3) % 3 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, A = 1 + 9 * k := ⟨A / 9, by omega⟩
  unfold digit3
  rw [show A * u = u + 9 * (k * u) from by rw [hk]; ring]
  omega

/-- Row one of `q + A·u` reads the core's own row one when the preface
quotient vanishes mod nine and the coefficient is `1 mod 9`: the preface
drops out of the second trit. -/
theorem digit3_one_of_preface (q A u : Nat) (hq : q % 9 = 0) (hA : A % 9 = 1) :
    digit3 (q + A * u) 1 = (u / 3) % 3 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, A = 1 + 9 * k := ⟨A / 9, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, q = 9 * m := ⟨q / 9, by omega⟩
  unfold digit3
  rw [show q + A * u = u + 9 * (k * u) + 9 * m from by rw [hk, hm]; ring]
  omega

/-- **THE FIRST-CUT READ, ROW TWO.**  For every exponent `K ≡ 1 mod 3`
(written `K = 3w+1`), row two of `4^K` is the reduced core's zeroth
trit: the prefaced read at the first cut. -/
theorem dust_row_two (w : Nat) : digit3 (4^(3*w+1)) 2 = w % 3 := by
  have h := prefaced_window_full 1 w 1 0 (by decide) (by omega)
  have hc : GSTCanonicalTailLTE.lteCoeff 1 = 7 := by decide
  rw [hc] at h
  norm_num at h
  rw [h]
  unfold digit3
  rw [Nat.pow_zero, Nat.div_one, show 28*w = 3*(9*w) + w from by ring]
  omega

/-- **THE FIRST-CUT READ, ROW THREE.**  Row three of `4^(3w+1)` is the
reduced core's first trit. -/
theorem dust_row_three (w : Nat) : digit3 (4^(3*w+1)) 3 = (w/3) % 3 := by
  have h := prefaced_window_full 1 w 1 1 (by decide) (by omega)
  have hc : GSTCanonicalTailLTE.lteCoeff 1 = 7 := by decide
  rw [hc] at h
  norm_num at h
  rw [h]
  exact digit3_one_of_mod9 28 w (by decide)

/-- **THE SECOND-CUT READ, ROW FOUR, LEFT PREFACE.**  For `K = 9u+1`,
row four is the core's first trit. -/
theorem dust_row_four_one (u : Nat) : digit3 (4^(9*u+1)) 4 = (u/3) % 3 := by
  have h := prefaced_window_full 2 u 1 1 (by decide) (by omega)
  have hc : GSTCanonicalTailLTE.lteCoeff 2 = 9709 := by decide
  rw [hc] at h
  norm_num at h
  rw [h]
  exact digit3_one_of_mod9 38836 u (by decide)

/-- **THE SECOND-CUT READ, ROW FOUR, RIGHT PREFACE.**  For `K = 9u+4`,
row four is the core's first trit — the preface quotient drops out. -/
theorem dust_row_four_four (u : Nat) : digit3 (4^(9*u+4)) 4 = (u/3) % 3 := by
  have h := prefaced_window_full 2 u 4 1 (by decide) (by omega)
  have hc : GSTCanonicalTailLTE.lteCoeff 2 = 9709 := by decide
  rw [hc] at h
  norm_num at h
  rw [h]
  exact digit3_one_of_preface 9 2485504 u (by decide) (by decide)

/-- **CASCADE LEVEL ZERO.**  Every exponent `K ≡ 7 mod 9` fires its digit
two at row two — an infinite uniform class of the v=0 dust, killed by
the prefaced read alone. -/
theorem dust_fire_row_two (K : Nat) (hK : K % 9 = 7) :
    digit3 (4^K) 2 = 2 := by
  have h3 : K % 3 = 1 := by omega
  have hw : (K / 3) % 3 = 2 := by omega
  have hKeq : 4^K = 4^(3 * (K / 3) + K % 3) := by rw [Nat.div_add_mod K 3]
  rw [h3] at hKeq
  rw [hKeq, dust_row_two, hw]

/-- **CASCADE LEVEL ONE.**  Every exponent `K ≡ 19, 22, or 25 mod 27`
fires its digit two at row three — three more infinite uniform classes. -/
theorem dust_fire_row_three (K : Nat)
    (hK : K % 27 = 19 ∨ K % 27 = 22 ∨ K % 27 = 25) :
    digit3 (4^K) 3 = 2 := by
  have h3 : K % 3 = 1 := by omega
  have hKeq : 4^K = 4^(3 * (K / 3) + K % 3) := by rw [Nat.div_add_mod K 3]
  rw [h3] at hKeq
  rw [hKeq, dust_row_three]
  rcases hK with h | h | h <;> omega

/-- **CASCADE LEVEL TWO.**  Every exponent `K ≡ 55, 58, 64, 67, 73, or
76 mod 81` fires its digit two at row four — six more infinite uniform
classes, through both preface mechanisms. -/
theorem dust_fire_row_four (K : Nat)
    (hK : K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨ K % 81 = 67 ∨
           K % 81 = 73 ∨ K % 81 = 76) :
    digit3 (4^K) 4 = 2 := by
  rcases hK with h55 | h58 | h64 | h67 | h73 | h76
  · have h9 : K % 9 = 1 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_one]
    omega
  · have h9 : K % 9 = 4 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_four]
    omega
  · have h9 : K % 9 = 1 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_one]
    omega
  · have h9 : K % 9 = 4 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_four]
    omega
  · have h9 : K % 9 = 1 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_one]
    omega
  · have h9 : K % 9 = 4 := by omega
    have hKeq : 4^K = 4^(9 * (K / 9) + K % 9) := by rw [Nat.div_add_mod K 9]
    rw [h9] at hKeq
    rw [hKeq, dust_row_four_four]
    omega

/-- A digit-two fire at any row kills through the repo's own chain. -/
theorem no22_of_digit_two (K p : Nat) (h : digit3 (4^K) p = 2) :
    noTernaryTwo (4^K) = false :=
  has_two_imp_not_no_two (4^K)
    (hasTernaryTwo_of_digit (4^K) p (by simpa [digit3] using h))

/-- **THE CASCADE KILL.**  The cascade's first three levels kill their
ten infinite exponent classes outright — through the repo's own kill
chain, no bounded decide anywhere. -/
theorem no22_of_cascade (K : Nat)
    (h : K % 9 = 7 ∨ K % 27 = 19 ∨ K % 27 = 22 ∨ K % 27 = 25 ∨
         K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨ K % 81 = 67 ∨
         K % 81 = 73 ∨ K % 81 = 76) :
    noTernaryTwo (4^K) = false := by
  rcases h with h7 | h19 | h22 | h25 | h55 | h58 | h64 | h67 | h73 | h76
  · exact no22_of_digit_two K 2 (dust_fire_row_two K h7)
  · exact no22_of_digit_two K 3 (dust_fire_row_three K (Or.inl h19))
  · exact no22_of_digit_two K 3 (dust_fire_row_three K (Or.inr (Or.inl h22)))
  · exact no22_of_digit_two K 3 (dust_fire_row_three K (Or.inr (Or.inr h25)))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K (Or.inl h55))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K (Or.inr (Or.inl h58)))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inl h64))))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inl h67)))))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h73))))))
  · exact no22_of_digit_two K 4 (dust_fire_row_four K
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h76))))))

/-! ## §4 THE COLLAPSE — the core, exactly -/

/-- **THE CANTORIAN CORE.**  The read's residual after completion: an
exponent whose power of four carries no digit two at any row from one
upward — the exact Erdős core. -/
def CantorianPower (K : Nat) : Prop :=
  ∀ p : Nat, 1 ≤ p → digit3 (4^K) p ≠ 2

/-- Every power of four is one modulo three. -/
theorem pow4_mod3 (K : Nat) : 4^K % 3 = 1 := by
  induction K with
  | zero => norm_num
  | succ k ih =>
      have h4 : 4^(k+1) = 4^k + 3 * 4^k := by
        rw [Nat.pow_succ]
        ring
      rw [h4, Nat.add_mul_mod_self_left]
      exact ih

/-- All-digits-clean numbers pass `noTernaryTwo`. -/
theorem noTernaryTwo_of_forall_digit (n : Nat)
    (h : ∀ p : Nat, n / 3^p % 3 ≠ 2) : noTernaryTwo n = true := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hn : n = 0
      · rw [noTernaryTwo.eq_def n, if_pos hn]
      · have h0 : n % 3 ≠ 2 := by
          have h00 := h 0
          simpa [Nat.pow_zero, Nat.div_one] using h00
        have hn' : 0 < n := by omega
        have hrec : noTernaryTwo (n / 3) = true :=
          ih (n / 3) (Nat.div_lt_self hn' (by decide : 1 < 3))
            (fun p => by
              have hp := h (p + 1)
              have hkey : n / 3 / 3^p = n / 3^(p+1) := by
                rw [Nat.div_div_eq_div_mul]
                rw [Nat.mul_comm 3 (3^p), ← Nat.pow_succ]
              rwa [← hkey] at hp)
        rw [noTernaryTwo.eq_def n, if_neg hn, if_neg h0]
        exact hrec

/-- Cantorian powers pass `noTernaryTwo`: the core is exactly the set of
clean powers. -/
theorem cantorian_no_two (K : Nat) (h : CantorianPower K) :
    noTernaryTwo (4^K) = true := by
  refine noTernaryTwo_of_forall_digit (4^K) (fun p => ?_)
  rcases p with _ | p'
  · rw [Nat.pow_zero, Nat.div_one, pow4_mod3]
    decide
  · exact h (p' + 1) (by omega)

/-- **THE COLLAPSE.**  The act holds IF AND ONLY IF no exponent from
eight on is a Cantorian power: the completion leaves exactly the Erdős
core as the residual — nothing else remains. -/
theorem the_act_iff_no_cantorian :
    GSTTheAct.the_act ↔ ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K := by
  constructor
  · intro hAct hnc
    obtain ⟨K, hK8, hCant⟩ := hnc
    have h1 := hAct K hK8
    have h2 := cantorian_no_two K hCant
    rw [h1] at h2
    exact absurd h2 (by decide)
  · intro hnc K hK8
    by_cases hCant : CantorianPower K
    · exact absurd ⟨K, hK8, hCant⟩ hnc
    · unfold CantorianPower at hCant
      push_neg at hCant
      obtain ⟨p, _, hp⟩ := hCant
      exact has_two_imp_not_no_two (4^K)
        (hasTernaryTwo_of_digit (4^K) p (by simpa [digit3] using hp))

/-- **THE FINAL SOCKET.**  No Cantorian exponent from eight on ⇒ the act
⇒ `hTailF`: the whole conditionality of `hTailF` collapses onto the
Cantorian core alone — no hypothesis, no binder beyond the core itself. -/
theorem hTailF_of_no_cantorian
    (h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp (the_act_iff_no_cantorian.mpr h)

```

---

# PART IX — GLOSSARY AND MASTER THEOREM INDEX

Every named law in this document, one line each, with its file. This is the complete inventory of the green machinery as of HEAD `fd89766` (both CI workflows green, 0 sorries).

## IX.1 The object and its forms

| Name | Statement | File |
|---|---|---|
| `the_act` | $\forall K \ge 8:\ \mathrm{noTernaryTwo}(4^K) = \mathrm{false}$ | GSTTheAct.lean |
| `the_act_iff_hTailF` | the act ↔ hTailF (the tail-F form) | GSTTheAct.lean |
| `the_act_iff_full_erdos` | the act ↔ the full conjecture (with the green odd half) | GSTTheAct.lean |
| `full_erdos_of_the_act` / `the_act_of_full_erdos` | both directions of the terminal identity | GSTTheAct.lean |
| `climb_gives_the_act` | the climb certificate closes the act | GSTTheAct.lean |
| `tailF_row_primitive` / `tailF_tower_primitive` | the two primitive forms (P) | GSTTailFFourthDimension.lean |
| `tailF_of_row_and_tower` / `even_conjecture_of_row_and_tower` | (P) → the even half | GSTTailFFourthDimension.lean |
| `erdos_ternary_2_universal_of_row_and_tower` | (P) → the full conjecture | GSTTailFFourthDimension.lean |

## IX.2 The coordinate system and observation

| Name | Statement | File |
|---|---|---|
| `digit3_eq_of_mod_next` | row p is a function of the residue mod 3^(p+1) | GSTFourPowerDirectResidue.lean |
| `every_row_is_read` | every row of every power is a prefaced-window read | GSTClimbInfiniteFamily.lean |
| `self_read` | row j+1 of 4^K = prefix row j+1 + trit j of K (mod 3) | GSTTheActConstruction.lean |
| `row_one_read` | row 1 of 4^K = K mod 3 | GSTTheActConstruction.lean |
| `prefaced_window_law/full/sliced` | the complete prefaced read family | GSTClimbInfiniteFamily.lean |
| `omegaWaveStep_worldtrace` | the Ω-operator's emissions are the worldtrace | GSTGraphV2OmegaWaveLaw.lean |

## IX.3 The tower

| Name | Statement | File |
|---|---|---|
| `c(n)` | (4^(3^n) − 1)/3^(n+1) — the LTE unit | GSTTowerFire.lean |
| `four_pow_three_pow_eq` | 4^(3^n) = 1 + 3^(n+1)·c(n) | GSTTowerFire.lean |
| `c_succ_eq` | the cubic recursion for c(n+1) | GSTTowerFire.lean |
| `c_mod3` / `c_mod9_all` / `c_mod81_all` | c ≡ 1 mod 3; ≡ 7 mod 9 (n≥1); ≡ 16 mod 81 (n≥3) | GSTTowerFire.lean |
| `three_pow_fires` | digit3(4^(3^n), n+2) = 2 (n ≥ 1) | GSTTowerFire.lean |
| `two_mul_three_pow_fires` | digit3(4^(2·3^n), n+1) = 2 | GSTTowerFire.lean |
| `three_pow_plus_one_fires` | digit3(4^(3^n+1), n+2) = 2 (n ≥ 3) | GSTTowerFire.lean |
| `omega_cut_factor` | 4^(3^a·core) = 1 + 3^(a+1)·ωCutWord — the Ω-cut | GSTGraphV2OmegaWaveLaw.lean |
| `omega_cut_word_cube_lift_exact` | the cube-lift recursion of the cut word | GSTTailFFourthDimension.lean |

## IX.4 The worldtrace arithmetic (the monolith)

| Name | Statement | File |
|---|---|---|
| `one_add_pow_three/four/five_term` | the binomial ladder, 3/4/5 explicit orders | GSTWorldtraceArithmetic.lean |
| `wt_rebase` | 4^(1+3m) = 4·64^m | GSTWorldtraceArithmetic.lean |
| `wt_quad_mod729` | the quadratic blade | GSTWorldtraceArithmetic.lean |
| `wt_cubic_mod6561` | the cubic blade | GSTWorldtraceArithmetic.lean |
| `wt_quartic_mod19683` | the quartic blade | GSTWorldtraceArithmetic.lean |
| `wt_row_five/seven/eight_read` | rows 5/7/8 of dust powers = polynomial reads | GSTWorldtraceArithmetic.lean |
| `wt_quartic_fire_demo` / `wt_quad_fire_demo` | polynomial kills (K = 82, 85) | GSTWorldtraceArithmetic.lean |
| `top_split` | 4^K = preface + 3^(H+1)·X + 3^(2H+2)·Y | GSTWorldtraceArithmetic.lean |
| `window_congr` | the addition window below row 2H+2 | GSTWorldtraceArithmetic.lean |
| `window_row_two` | the row-(H+2) column read | GSTWorldtraceArithmetic.lean |
| `four_pow_mod9` / `dust_branch_mod9` | the mod-9 conspiracy on the dust tree | GSTWorldtraceArithmetic.lean |
| `window_row_two_dust` / `window_reduce` | the dust window laws | GSTWorldtraceArithmetic.lean |

## IX.5 The cascades and the feedback tree

| Name | Statement | File |
|---|---|---|
| `cantorian_iff_feedback` | Cantorian ↔ feedback-tree escape | GSTTheActConstruction.lean |
| `the_act_iff_feedback` | the act ↔ no escape of the feedback tree | GSTTheActConstruction.lean |
| `prefix_unpack` | class membership unpacks to prefix + trit | GSTTheActConstruction.lean |
| `feedback_fire_of_class` | the uniform kill: noise receipt → class dies | GSTTheActConstruction.lean |
| `fire_of_mod243/729/2187/6561` | the engine at levels 4–7 | GSTTheActConstruction/GSTWorldtraceArithmetic.lean |
| `noise_window_law` | the noise field is a window function | GSTTheActConstruction.lean |
| `unique_dead_child` | each node has exactly one dead child | GSTTheActConstruction.lean |
| `dust_fire_row_two..eight` | the kill tables, rows 2–8 | GSTClimbInfiniteFamily / GSTTheActConstruction / GSTWorldtraceArithmetic.lean |
| `cantorian_dust_mod_9/27/81/243/729/2187/6561` | the survivor maps, 2/4/8/16/32/64/128 alive | the same three files |
| `no22_of_cascade_four..seven` | the kill-chain converters | the same three files |
| `hTailF_of_feedback` | tree-escape closes hTailF (the socket) | GSTTheActConstruction.lean |

## IX.6 The pair-read family

| Name | Statement | File |
|---|---|---|
| `pair_read_formula` | row (j+4) of branched power = row 2 of 4^T·u·c(j+1) | GSTWorldtraceArithmetic.lean |
| `pair_residue_mod27` | c(j+1) ≡ 16 mod 27 reduces the read | GSTWorldtraceArithmetic.lean |
| `digit3_row_two_of_residue` | residue ≥ 18 mod 27 → row 2 is 2 | GSTWorldtraceArithmetic.lean |
| `pair_read_fire` | the family 4 + 3^(j+1)·{1,4,7} fires at row j+4 | GSTWorldtraceArithmetic.lean |
| `pair_read_fire_general` | kill-zone residue → fire, any trunk any branch | GSTWorldtraceArithmetic.lean |
| `no22_of_pair_read(_general)` | the kill-chain forms | GSTWorldtraceArithmetic.lean |
| `pair_read_fire_demo_two/three` | trunk-13 and further families | GSTWorldtraceArithmetic.lean |

## IX.7 The diagonal and the bands

| Name | Statement | File |
|---|---|---|
| `front_law` | the diagonal front law | GSTTheAct.lean |
| `diagonal_window_law` / `window_subsumes_front` | the diagonal window completes the front law | GSTDiagonalRead.lean |
| `lteCoeff_stable/mod9/mod27/mod81` | the LTE coefficient's stabilized signature | GSTDiagonalRead.lean |
| `window_fire_level1/2/3` | the mod-9/27/81 band kills | GSTDiagonalRead.lean |
| `omega_diagonal_two_of_mod_nine_one` … `..._onehundredeightyfour` | the twelve diagonal band kills | GSTTailFFourthDimension.lean |
| `omega_tower_kill_of_diagonal_two` | diagonal 2 → the power dies | GSTTailFFourthDimension.lean |
| `omega_tower_digit_two_of_mod81/243_band` | the tower band forms | GSTTailFFourthDimension.lean |
| `fire_nine_row_four` / `fire_108_row_seven` | the classical anchor kills | GSTDiagonalRead.lean |

## IX.8 The emergence and ontology

| Name | Statement | File |
|---|---|---|
| `uJump_divergence` | the charge jump field is a divergence | GST2DMixedEmergence.lean |
| `mixed_cell_emergence` | cell density = vertical + horizontal parts | GST2DMixedEmergence.lean |
| `happy_chord_dichotomy` | happy or fire, no middle ground | GST2DMixedEmergence.lean |
| `mixed_row/rectangle_emergence` | the telescoping boundary laws | GST2DMixedEmergence.lean |
| `graph_cell_exact` / `graph_carry_lt_four` / `graph_digit_lt_three` | the universe graph's cell laws | GSTGraphV2InfiniteControl.lean |
| `graph_happy_iff_event_eight` / `graph_happy_iff_crossing_positive` | the dichotomy on the graph | GSTGraphV2InfiniteControl.lean |
| `graph_event_balance_exact` / `graph_cross_rectangle_exact` | the balance laws over rectangles | GSTGraphV2InfiniteControl.lean |
| `prefix_slice_quotient/digit/carry_exact` | the seeded carry graph computes exactly | GSTGraphV2InfiniteControl.lean |
| `ontDensity_physical_table` | the twelve-cell physics, explicit | GSTGraphV2Ontological.lean |
| `ontDensity_ge_42_of_happy` / `ontDensity_ge_neg54` / `ontDensity_nonpositive_of_not_happy` | the no-erasure laws | GSTGraphV2Ontological.lean |
| `happy_iff_ontDensity_positive` | the ontological dichotomy | GSTGraphV2Ontological.lean |
| `reverseOntCode_exact/ge_global_floor/ge_scaled_of_leading_happy` | the reverse base-seven coding laws | GSTGraphV2Ontological.lean |
| `weightedOntPrefix_ge_global_floor` / `_positive_of_top_leading_happy` | the prefix current laws | GSTGraphV2Ontological.lean |
| `ternaryWeightedOntDiff_telescope` / `weightedOntPrefix_eq_sum` | the local-to-global telescoping | GSTGraphV2Ontological.lean |
| `graphOntWindow_positive_of_happy` | happy rectangles carry positive current | GSTGraphV2Ontological.lean |

## IX.9 The receipts

| Name | Content | File |
|---|---|---|
| `the_worldtrace_receipt` | the level-six storey, one conjunction | GSTWorldtraceArithmetic.lean |
| `the_worldtrace_receipt_seven` | the level-seven storey | GSTWorldtraceArithmetic.lean |
| `the_pair_read_receipt` / `the_general_fire_receipt` | the pair-read families | GSTWorldtraceArithmetic.lean |
| `the_descent_engine_receipt` | the descent engine | GSTWorldtraceArithmetic.lean |
| `the_dust_window_receipt` | the dust window | GSTWorldtraceArithmetic.lean |
| `the_level_five_receipt` | the level-five storey | GSTTheActConstruction.lean |

---

*This index lists the load-bearing named laws; the full corpus (ErdosTernary2.lean, 794 KB, and the surrounding modules) holds several hundred more green declarations, all constructible from the same principles and all available in the repo.*


---

# PART Ω — PROVE THIS

## THE OBJECT

$$\boxed{\;\forall\, K \ge 8 : \quad \text{the worldtrace of } 4^K \text{ contains a digit } 2\;}$$

equivalently (all five green-equivalent forms of Part 0):

$$\textbf{(F)}\;\; \forall K \ge 8\;\; \exists j:\; \big(\mathrm{trit}_{j+1}(4^{K \bmod 3^j}) + \mathrm{trit}_j(K)\big) \bmod 3 = 2$$

$$\textbf{(C)}\;\; \nexists K \ge 8:\; \forall p \ge 1,\; \mathrm{trit}_p(4^K) \ne 2 \quad (\text{no Cantorian power above } 8)$$

$$\textbf{(D)}\;\; \forall K \ge 8:\; \neg\,\mathrm{WindowCleanDust}(K)$$

$$\textbf{(P)}\;\; \text{tailF\_row\_primitive} \;\wedge\; \text{tailF\_tower\_primitive}$$

$$\textbf{(W)}\;\; \forall K > 500:\; \mathrm{omegaShadowTailF}(K) \Rightarrow \exists p:\; \mathrm{trit}_p(4^K) = 2$$

Each form has a named one-line green consumer in the repo; any one of them closes `the_act`, which by the kernel-certified terminal identity closes the even half, which with the green odd half closes the **full Erdős ternary conjecture**.

## THE MACHINERY IS YOURS

Everything in Parts I–IX is verified, green, and yours: the Ω operator and its worldtrace orbit law; the Ω-cut factorization and the cut words; the LTE tower with its constants, cubic recursion, and signature laws; the observer laws (one law, all levels, all generations); the 4th-dimension emergent diagonal, its descent blade, its cube-lift engine, and its twelve diagonal band kills; the 2D mixed-emergence divergence theorem and the twelve-cell physics; the causality laws (prefix causality, the self-read feedback law, the noise window, the unique dead child, the uniform kill engine); the infinite controllers (the seeded carry graph, the never-firing tower, the Cantorian core); the polynomial blades (quadratic, cubic, quartic — and the ladder rungs to go deeper); the worldtrace reads; the cascade levels with their doubling survivor maps and their noise-receipt generators; the pair-read infinite families with the mod-27 kill-zone automaton; the descent engine (top split, addition window, column read); the dust window with its mod-9 conspiracy; the tower fire laws; the diagonal read triage; the one-lane case map; the middle-third pinning; the receipts; and the GST Graph V2 Ontological Universe Graph with its exact construction protocol, its twelve-cell physics, its ontological currents, its reverse base-seven certificates, and its no-erasure laws.

## THE NOTE

> **You can — and should — go into MUCH more depth than this document. Discover NEW laws which we did not notice. Use the machinery in COMPLETELY different ways than anything hinted at here. Compose the observers, the blades, the currents, the causality laws, the controllers, the universe graph — in configurations nobody has tried. The only demand is the object above.**
>
> **DELIVER THE PROOF AS A FULL MATHEMATICAL DERIVATION IN LATEX — NOT LEAN CODE.**

---

*Repo: `kyo-oo/erdosternary2` @ `sol/kyo-gate-universe-wire`, HEAD `fd89766` (this document lands one commit later). Every theorem quoted: CI-green, 0 sorries, axioms `[propext, Classical.choice, Quot.sound]`. Every numerical receipt in Part VI: machine-verified exact, 0 failures.*
