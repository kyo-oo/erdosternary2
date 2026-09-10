import GSTInfiniteFourPowerNavigation
import GSTGraphV2HandwrittenOmegaUBlock
import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2OmegaWaveLaw

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GST2DMixedEmergence
open GSTU2DEventTransport

/-!
# THE Ω-WAVE LAW — the final stroke of the GST Ontological V2 Graph route

This file is the Law of the ontology: one theorem-package that *confirms
existence* of the ternary-two witness for every exponent in its domain and
*explains why*, by combining exactly the three mandated weapons:

1. **A genuine new operator** — `omegaWaveStep`, the Ω-wave transfusion:
   one simultaneous handwritten-U multiply/divide action on a seeded
   information word (the origin trit is consumed into the x4 seed while the
   remaining origin is divided by three).

2. **The Omega infinity hand-written equations** — the exact LTE tower
   `pow4_three_power_lte_exact` / `lteCoeff_mod3_one` together with the
   handwritten-U origin split of the omega block.

3. **The infinite controller** — the all-depth bad coupled control and the
   latent gate transfer of the Graph-V2 controller bridge.

The mathematical heart is the **Ω-cut tower**.  For an exponent
`K = 3^a * core`, the power `4^K` admits the exact decomposition

    4^K = 1 + 3^(a+1) * (lteCoeff a * omegaGeoSum a core),

and the ternary digit of `4^K` at the cut row `a+1` is **literally the
first nonzero ternary trit of the exponent**:

    digit3 (4^K) (a+1) = core % 3,

with cut carry exactly zero for `a ≥ 1` (the prefix at the cut is one).
Hence every exponent whose core is congruent to two modulo three **owns a
physical Happy row exactly at its own LTE cut** — an infinite arithmetic
family (all `K = 3^a * core`, `a ≥ 1`, `core ≡ 2 (mod 3)`) that no previous
theorem of the repository covered.  One level higher, the cut word satisfies
`W ≡ 7 * core (mod 9)` for `a ≥ 1`, giving digit two at row `a+2` for every
core congruent to `1, 5, 6 (mod 9)` — the second infinite family.  The tower
coefficients stabilize: `lteCoeff a` is constant modulo `3^L` for every
`a ≥ L-1`, the arithmetic form of the controller's "observation depth is
arbitrary".

The **why** is delivered twice: arithmetically — the mean factor
`lteCoeff ≡ 1 (mod 3)` preserves the exponent's first nonzero trit through
the transfusion, so the creation digit cannot be destroyed by climbing —
and ontologically — the Ω transfusion conserves all seven axes of the
Graph-V2 vertex (`residual_parent_observables_exact`), a Happy gate
re-encodes into latent carry rather than annihilating
(`graph_child_happy_latent_transfer`), and an all-bad unit sheet generates
the full infinite bad coupled controller (`graph_infinite_bad_control`)
which is then punctured by its own LTE cut: the controller forbids exactly
what the cut provides.
-/

/-! ## §1 The genuine new operator: the Ω-wave transfusion

The operator acts on a seeded information word `(D, X)`.  In one action it

* consumes the least ternary trit of `X` into the x4 seed (the
  handwritten-U multiply: the seed advances by the exact carry law
  `(D + 4·trit)/3`), and
* divides the remaining origin by three (the handwritten-U divide).

It is the local, nameable form of the simultaneous U action that the
handwritten omega equations perform on perfect powers.
-/

/-- **THE NEW OPERATOR ΩW** — one omega wave-climb transfusion step on a
seeded information word: the origin trit is consumed into the x4 seed while
the remaining origin is divided by three. -/
def omegaWaveStep (D X : Nat) : Nat × Nat :=
  ((D + 4 * (X % 3)) / 3, X / 3)

/-- The operator consumes the origin trit exactly as the handwritten-U
divide: the word splits into its consumed trit and its U-tail, and the tail
is literally the operator's second component. -/
theorem omegaWaveStep_u_divide (D X : Nat) :
    X = originTrit X + 3 * (omegaWaveStep D X).2 :=
  origin_split_exact X

/-- The operator's seed action is the exact x4 cell carry law: the consumed
trit is multiplied into the seed and the result re-divided by three, with
the visible output digit emitted as remainder. -/
theorem omegaWaveStep_u_multiply (D X : Nat) :
    D + 4 * originTrit X =
      3 * (omegaWaveStep D X).1 + ((D + 4 * originTrit X) % 3) := by
  unfold omegaWaveStep originTrit
  omega

/-- Mass conservation of one transfusion: seed plus quadrupled trit is
exactly the tripled new seed plus the visible output. -/
theorem omegaWaveStep_mass (D X : Nat) :
    3 * (omegaWaveStep D X).1 ≤ D + 4 * originTrit X ∧
      D + 4 * originTrit X < 3 * ((omegaWaveStep D X).1 + 1) := by
  unfold omegaWaveStep originTrit
  constructor <;> omega

/-- **The worldtrace orbit law.**  The vertical step of the exact carry
stream of any energy `R` is literally one Ω-wave transfusion of the seeded
tail: the operator's orbit *is* the information wave that reads the ternary
digits of `R`. -/
theorem omegaWaveStep_worldtrace (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).1 = carry4 R (p+1) :=
  (carry4_forward_exact R p).symm

/-- The transfusion tail descends the ternary ladder exactly one rung. -/
theorem omegaWaveStep_tail (R p : Nat) :
    (omegaWaveStep (carry4 R p) (R / 3^p)).2 = R / 3^(p+1) := by
  unfold omegaWaveStep
  rw [← Nat.div_div_eq_div_mul]
  rfl

/-! ## §2 The Ω-cut tower (the LTE trail) -/

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
decomposes exactly as one plus the cut modulus times the cut word, and the
cut word is the product of the LTE mean and the geometric mean. -/
theorem omega_cut_factor (a core : Nat) :
    4^(3^a * core) =
      1 + 3^(a+1) * omegaCutWord a core := by
  induction core with
  | zero =>
      have h0 : 3^a * 0 = 0 := Nat.mul_zero _
      rw [h0, Nat.pow_zero]
      simp [omegaGeoSum, omegaCutWord]
  | succ core ih =>
      have hbase := pow4_three_power_lte_exact a
      have hstep : 4^(3^a * (core+1)) = 4^(3^a * core) * 4^(3^a) := by
        rw [← Nat.pow_add]
        congr 1
        ring
      have hterm : (4^(3^a))^core = 4^(3^a * core) := by
        rw [Nat.pow_mul]
      have hgeoW : omegaCutWord a (core+1)
          = omegaCutWord a core + lteCoeff a * 4^(3^a * core) := by
        unfold omegaCutWord omegaGeoSum
        simp only [Finset.sum_range_succ, hterm]
        ring
      rw [hstep, ih, hbase, hgeoW, ih]
      ring

/-- Every term of the geometric mean is one modulo three. -/
theorem omega_geo_term_mod3 (a j : Nat) :
    ((4^(3^a))^j) % 3 = 1 := by
  rw [Nat.pow_mod, pow4_mod3_one, Nat.one_pow] <;> omega

/-- The geometric mean is the core mass modulo three. -/
theorem omega_geo_mod3 (a core : Nat) :
    omegaGeoSum a core % 3 = core % 3 := by
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, omega_geo_term_mod3, ih]
      omega

/-- **THE ν-LAW (level one of the Ω-cut tower).**  The ternary digit of
`4^(3^a * core)` at the cut row `a+1` is literally the first nonzero
ternary trit of the exponent: the residue of the core mass modulo three. -/
theorem omega_cut_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+1) = core % 3 := by
  have hf := omega_cut_factor a core
  have hp : 0 < 3^(a+1) := Nat.pow_pos (by decide)
  have h1 : 1 < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hdiv : (1 + 3^(a+1) * omegaCutWord a core) / 3^(a+1)
      = omegaCutWord a core := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt h1, Nat.zero_add]
  unfold digit3
  rw [hf, hdiv, omegaCutWord, Nat.mul_mod, lteCoeff_mod3_one,
    omega_geo_mod3, Nat.one_mul]
  omega

/-- The prefix of the power at the cut row is exactly one. -/
theorem omega_cut_prefix_one (a core : Nat) :
    4^(3^a * core) % 3^(a+1) = 1 :=
  pow4_scaled_mod_next a core

/-- **The cut carry law.**  From sheet level one onward the cut carry is
exactly zero: the quadrupled unit prefix stays below the cut modulus. -/
theorem omega_cut_carry_zero (a core : Nat) (ha : 1 ≤ a) :
    carry4 (4^(3^a * core)) (a+1) = 0 := by
  have h9 : (4:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^2 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 2 ≤ a+1)
    norm_num at h3
    omega
  unfold carry4
  rw [omega_cut_prefix_one]
  have h41 : (4:Nat) * 1 < 3^(a+1) := by simpa using h9
  exact Nat.div_eq_of_lt h41

/-- **THE Ω-CUT GATE (level one).**  Every exponent whose core mass is
congruent to two modulo three owns a physical Happy row exactly at its own
LTE cut — digit two with carry zero.  This is an infinite arithmetic family:
all `K = 3^a * core` with `a ≥ 1` and `core ≡ 2 (mod 3)`. -/
theorem omega_cut_happy_gate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    HappyCell
      (carry4 (4^(3^a * core)) (a+1))
      (digit3 (4^(3^a * core)) (a+1)) := by
  refine ⟨?_, Or.inl ?_⟩
  · rw [omega_cut_digit a core, hcore]
  · rw [omega_cut_carry_zero a core ha]

/-! ## §3 Level two of the tower and the stabilization -/

/-- The LTE mean is constant modulo nine from sheet level one onward. -/
theorem omega_lteCoeff_mod9 (a : Nat) (ha : 1 ≤ a) :
    lteCoeff a % 9 = 7 := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        decide
      · have ha' : 1 ≤ a := hpos
        have hc := ih ha'
        have h1 : 3^(a+1) % 9 = 0 := by
          have hsplit : 3^(a+1) = 3^2 * 3^(a+1-2) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have hmod : (3^2 * 3^(a+1-2)) % 3^2 = 0 := Nat.mul_mod_left _ _
          rw [hsplit]
          exact hmod
        have h2 : 3^(2*a+1) % 9 = 0 := by
          have hsplit : 3^(2*a+1) = 3^2 * 3^(2*a+1-2) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          have hmod : (3^2 * 3^(2*a+1-2)) % 3^2 = 0 := Nat.mul_mod_left _ _
          rw [hsplit]
          exact hmod
        have hA : (3^(a+1) * (lteCoeff a)^2) % 9 = 0 := by
          rw [Nat.mul_mod, h1, Nat.zero_mul]
        have hB : (3^(2*a+1) * (lteCoeff a)^3) % 9 = 0 := by
          rw [Nat.mul_mod, h2, Nat.zero_mul]
        have hunfold : lteCoeff (a+1)
            = lteCoeff a + 3^(a+1) * (lteCoeff a)^2
              + 3^(2*a+1) * (lteCoeff a)^3 := rfl
        rw [hunfold]
        omega

/-- The base of the geometric mean is one modulo nine from sheet level one
onward. -/
theorem omega_base_mod9 (a : Nat) (ha : 1 ≤ a) :
    (4^(3^a)) % 9 = 1 := by
  induction a with
  | zero => omega
  | succ a ih =>
      rcases Nat.eq_zero_or_pos a with h0 | hpos
      · subst h0
        norm_num
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hpos]
        norm_num

/-- The geometric mean is the core mass modulo nine from sheet level one
onward. -/
theorem omega_geo_mod9 (a core : Nat) (ha : 1 ≤ a) :
    omegaGeoSum a core % 9 = core % 9 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 9 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod9 a ha, Nat.one_pow] <;> omega
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-two cut word law.**  From sheet level one onward the cut
word is `7 * core` modulo nine. -/
theorem omega_cut_word_mod9 (a core : Nat) (ha : 1 ≤ a) :
    omegaCutWord a core % 9 = (7 * core) % 9 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod9 a ha, omega_geo_mod9 a core ha]
  omega

/-- **THE LEVEL-TWO DIGIT LAW.**  The ternary digit of `4^(3^a * core)` at
row `a+2` is the top trit of the cut word, i.e. the top trit of
`7 * core` modulo nine.  Delivered through the green prefix-slice socket of
the infinite controller: the cut decomposition `4^K = 1 + 3^(a+1) * W` is
literally a prefix/tail slice, so the digit two rows above the cut is the
cut word's own ternary digit at row one. -/
theorem omega_level2_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+2) = (omegaCutWord a core % 9) / 3 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 1 h1
  rw [show a+2 = (a+1)+1 from by omega, hf, hslice]
  unfold digit3
  rw [Nat.pow_one]
  omega

/-- **THE LEVEL-TWO GATE CLASSES.**  For every core congruent to one, five
or six modulo nine, the power `4^(3^a * core)` owns a ternary digit two at
row `a+2` — the second infinite family of the Law. -/
theorem omega_level2_digit_two (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 9 = 1 ∨ core % 9 = 5 ∨ core % 9 = 6) :
    digit3 (4^(3^a * core)) (a+2) = 2 := by
  rw [omega_level2_digit, omega_cut_word_mod9 a core ha]
  rcases hcore with h1 | h5 | h6
  · have hval : (7 * core) % 9 = 7 := by omega
    rw [hval]
    norm_num
  · have hval : (7 * core) % 9 = 8 := by omega
    rw [hval]
    norm_num
  · have hval : (7 * core) % 9 = 6 := by omega
    rw [hval]
    norm_num

/-! ## §4 The tower stabilization — the controller's "depth is arbitrary" -/

/-- One stabilization step: above the observation level the LTE mean does
not move modulo the level modulus. -/
theorem omega_lteCoeff_mod_step (a L : Nat) (ha : L ≤ a + 1) :
    lteCoeff (a+1) % 3^L = lteCoeff a % 3^L := by
  have h1 : 3^(a+1) % 3^L = 0 := by
    have hsplit : 3^(a+1) = 3^L * 3^(a+1-L) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod_left]
  have h2 : 3^(2*a+1) % 3^L = 0 := by
    have hsplit : 3^(2*a+1) = 3^L * 3^(2*a+1-L) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod_left]
  have hA : (3^(a+1) * (lteCoeff a)^2) % 3^L = 0 := by
    rw [Nat.mul_mod, h1, Nat.zero_mul]
  have hB : (3^(2*a+1) * (lteCoeff a)^3) % 3^L = 0 := by
    rw [Nat.mul_mod, h2, Nat.zero_mul]
  have hA0 : 3^(a+1) * (lteCoeff a)^2
      = 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L) := by
    have hdiv : (3^(a+1) * (lteCoeff a)^2) % 3^L
        + 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L)
        = 3^(a+1) * (lteCoeff a)^2 :=
      Nat.mod_add_div _ (3^L)
    rw [hA, Nat.zero_add] at hdiv
    exact hdiv.symm
  have hB0 : 3^(2*a+1) * (lteCoeff a)^3
      = 3^L * ((3^(2*a+1) * (lteCoeff a)^3) / 3^L) := by
    have hdiv : (3^(2*a+1) * (lteCoeff a)^3) % 3^L
        + 3^L * ((3^(2*a+1) * (lteCoeff a)^3) / 3^L)
        = 3^(2*a+1) * (lteCoeff a)^3 :=
      Nat.mod_add_div _ (3^L)
    rw [hB, Nat.zero_add] at hdiv
    exact hdiv.symm
  have hunfold : lteCoeff (a+1)
      = lteCoeff a + 3^(a+1) * (lteCoeff a)^2
        + 3^(2*a+1) * (lteCoeff a)^3 := rfl
  rw [hunfold, hA0]
  rw [show lteCoeff a + 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L)
        + 3^(2*a+1) * (lteCoeff a)^3
        = (lteCoeff a + 3^L * ((3^(a+1) * (lteCoeff a)^2) / 3^L))
          + 3^L * ((3^(2*a+1) * (lteCoeff a)^3) / 3^L) from by
      rw [hB0]]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]

/-- **THE TOWER STABILIZATION LAW** — the arithmetic form of the infinite
controller's "observation depth is arbitrary": from level `L-1` onward, the
LTE mean is constant modulo `3^L`.  The tower digits at level `L` therefore
depend only on the core residue for every sufficiently deep sheet. -/
theorem omega_lteCoeff_stable (L d : Nat) :
    lteCoeff ((L-1) + d) % 3^L = lteCoeff (L-1) % 3^L := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := omega_lteCoeff_mod_step ((L-1)+d) L (by omega)
      have hidx : (L-1) + (d+1) = ((L-1)+d) + 1 := by omega
      rw [hidx]
      exact hstep.trans ih

/-! ## §5 The controller puncture — the WHY, formal -/

/-- The unit sheet at column `K` reads exactly the digits and carries of
`4^K`. -/
theorem omega_unit_sheet (K p : Nat) :
    (graph 1 K p).seven.carry = carry4 (4^K) p ∧
      (graph 1 K p).seven.digit = digit3 (4^K) p := by
  constructor <;>
    simp [graph, cell, GSTCanonicalSevenAxisBridge.vertex, Nat.mul_one]

/-- An all-bad unit-sheet column (from row three downward) generates the
full infinite bad coupled controller of the Graph-V2 bridge. -/
theorem omega_all_bad_to_controller (K : Nat)
    (hbad : ∀ p : Nat, 3 ≤ p → ¬ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    GSTV2.InfiniteBadCoupledControl (4^K) (graphCoupledState 1 K 3) := by
  apply graph_infinite_bad_control 1 K 3
  · have h := (omega_unit_sheet 0 3).1
    rw [h]
    unfold carry4
    norm_num
  · intro j
    have hc := (omega_unit_sheet K (3+j)).1
    have hd := (omega_unit_sheet K (3+j)).2
    rw [show (graph 1 K (3+j)).seven.carry = carry4 (4^K) (3+j) from hc,
      show (graph 1 K (3+j)).seven.digit = digit3 (4^K) (3+j) from hd]
    exact hbad (3+j) (by omega)

/-- **THE CONTROLLER PUNCTURE.**  For the class-two family at sheet level
two or higher, an all-bad column is impossible: the LTE cut of that very
column is a physical Happy cell. -/
theorem omega_puncture (a core : Nat) (ha : 2 ≤ a) (hcore : core % 3 = 2) :
    ¬ (∀ p : Nat, 3 ≤ p →
        ¬ HappyCell (carry4 (4^(3^a * core)) p)
          (digit3 (4^(3^a * core)) p)) := by
  intro hbad
  exact hbad (a+1) (by omega) (omega_cut_happy_gate a core (by omega) hcore)

/-- **THE WHY (combined).**  For the class-two family at sheet level two or
higher, an all-bad unit-sheet column would simultaneously

* generate the full infinite bad coupled controller — the creation-blocked
  state of the ontology, and
* be punctured by its own LTE cut — a physical Happy cell.

Both cannot hold: the transfusion mean `lteCoeff ≡ 1 (mod 3)` preserves the
exponent's first nonzero trit, so the creation digit survives every climb
and the controller is contradicted by the very sheet it controls. -/
theorem omega_why_theorem (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core)
    (hbad : ∀ p : Nat, 3 ≤ p → ¬ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) :
    GSTV2.InfiniteBadCoupledControl (4^K) (graphCoupledState 1 K 3) ∧ False := by
  refine ⟨omega_all_bad_to_controller K hbad, ?_⟩
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  rw [hKac] at hbad
  exact omega_puncture a core ha hcore hbad

/-! ## §6 THE LAW — existence for the Ω-covered families -/

/-- The class-two family: exponents `K = 3^a * core` with `a ≥ 1` and core
congruent to two modulo three. -/
def omegaClassTwo (K : Nat) : Prop :=
  ∃ a core : Nat, 1 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core

/-- The level-two family: exponents `K = 3^a * core` with `a ≥ 1` and core
congruent to one, five or six modulo nine. -/
def omegaClassLevelTwo (K : Nat) : Prop :=
  ∃ a core : Nat, 1 ≤ a ∧
    (core % 9 = 1 ∨ core % 9 = 5 ∨ core % 9 = 6) ∧
    K = 3^a * core

/-- **THE Ω-WAVE EXISTENCE LAW, family one.**  Every class-two exponent
owns a physical Happy row (at its own LTE cut, row `a+1 ≥ 2`). -/
theorem omega_wave_existence_class_two (K : Nat) (hK : omegaClassTwo K) :
    ∃ p : Nat, 2 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+1, by omega, ?_⟩
  rw [hKac]
  exact omega_cut_happy_gate a core ha hcore

/-- **THE Ω-WAVE CLIMB FRAGMENT.**  Every class-two exponent at sheet level
two or higher satisfies the climb statement of the third-wave seam — a
fragment of `four_power_happy_climb`, delivered unconditionally. -/
theorem omega_wave_climb_class_two (K : Nat)
    (hK : ∃ a core : Nat, 2 ≤ a ∧ core % 3 = 2 ∧ K = 3^a * core) :
    ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+1, by omega, ?_⟩
  rw [hKac]
  exact omega_cut_happy_gate a core (by omega) hcore

/-- **THE Ω-WAVE EXISTENCE LAW, family two.**  Every level-two-family
exponent owns a ternary digit two at row `a+2 ≥ 3`. -/
theorem omega_wave_digit_two_class_level_two (K : Nat)
    (hK : omegaClassLevelTwo K) :
    ∃ p : Nat, 3 ≤ p ∧ digit3 (4^K) p = 2 := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  refine ⟨a+2, by omega, ?_⟩
  rw [hKac]
  exact omega_level2_digit_two a core ha hcore

/-- **The creation certificate of the class-two family** — the exact shape
consumed by the monolith's navigation seam, delivered at the LTE cut with
the carry-zero branch. -/
theorem omega_cut_certificate (a core : Nat) (ha : 1 ≤ a)
    (hcore : core % 3 = 2) :
    ∃ p : Nat, 1 ≤ p ∧ (4^(3^a * core)) / 3^p % 3 = 2 ∧
      ((4 * ((4^(3^a * core)) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^(3^a * core)) % 3^p)) / 3^p % 3 = 1 ∧
        (4^(3^a * core)) / 3^(p+1) % 3 = 2)) := by
  refine ⟨a+1, by omega, ?_, ?_⟩
  · show digit3 (4^(3^a * core)) (a+1) = 2
    rw [omega_cut_digit a core, hcore]
  · left
    have hc0 : (4 * ((4^(3^a * core)) % 3^(a+1))) / 3^(a+1) % 3 = 0 := by
      have hc := omega_cut_carry_zero a core ha
      unfold carry4 at hc
      rw [hc, Nat.zero_mod]
    exact hc0

#check omegaWaveStep
#check omegaWaveStep_worldtrace
#check omega_cut_factor
#check omega_cut_digit
#check omega_cut_happy_gate
#check omega_lteCoeff_mod9
#check omega_level2_digit_two
#check omega_lteCoeff_stable
#check omega_why_theorem
#check omega_wave_existence_class_two
#check omega_wave_climb_class_two
#check omega_wave_digit_two_class_level_two
#check omega_cut_certificate
#print axioms omegaWaveStep_worldtrace
#print axioms omega_cut_factor
#print axioms omega_cut_digit
#print axioms omega_cut_happy_gate
#print axioms omega_lteCoeff_mod9
#print axioms omega_level2_digit_two
#print axioms omega_lteCoeff_stable
#print axioms omega_why_theorem
#print axioms omega_wave_existence_class_two
#print axioms omega_wave_climb_class_two
#print axioms omega_wave_digit_two_class_level_two
#print axioms omega_cut_certificate

end GSTGraphV2OmegaWaveLaw

/-- Monolith transplant route: the class-two family's creation certificate,
delivered by the Ω-cut gate with no hypothesis of any kind.  This is the
Law's direct entry point into the navigation seam — an infinite arithmetic
family (all `K = 3^a * core`, `a ≥ 1`, `core ≡ 2 (mod 3)`) that previously
required the third-wave climb hypothesis. -/
theorem gst_four_power_creation_certificate_of_omega_cut
    (K : Nat) (hK : GSTGraphV2OmegaWaveLaw.omegaClassTwo K) :
    ∃ p : Nat, 1 ≤ p ∧ (4^K) / 3^p % 3 = 2 ∧
      ((4 * ((4^K) % 3^p)) / 3^p % 3 = 0 ∨
       ((4 * ((4^K) % 3^p)) / 3^p % 3 = 1 ∧
        (4^K) / 3^(p+1) % 3 = 2)) := by
  obtain ⟨a, core, ha, hcore, hKac⟩ := hK
  rw [hKac]
  exact GSTGraphV2OmegaWaveLaw.omega_cut_certificate a core ha hcore

#print axioms gst_four_power_creation_certificate_of_omega_cut
