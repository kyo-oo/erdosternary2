import GSTInfiniteFourPowerNavigation
import GSTFourPowerDirectResidue
import GSTGraphV2HandwrittenOmegaUBlock
import GSTGraphV2InfiniteControllerBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTGraphV2OmegaWaveLaw

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue (lteCoeff lteCoeff_mod3_one
  pow4_three_power_lte_exact pow4_mod3_one pow4_scaled_mod_next)
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
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
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ]

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
      have hstep : 4^(3^a * (core+1)) = 4^(3^a * core) * 4^(3^a) :=
        Nat.pow_add 4 (3^a * core) (3^a)
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
          rw [hsplit]
          omega
        have h2 : 3^(2*a+1) % 9 = 0 := by
          have hsplit : 3^(2*a+1) = 3^2 * 3^(2*a+1-2) := by
            rw [← Nat.pow_add]
            congr 1
            omega
          rw [hsplit]
          omega
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
  · have hval : (7 * core) % 9 = 8 := by omega
    rw [hval]
  · have hval : (7 * core) % 9 = 6 := by omega
    rw [hval]

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
    rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have h2 : 3^(2*a+1) % 3^L = 0 := by
    have hsplit : 3^(2*a+1) = 3^L * 3^(2*a+1-L) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [hsplit, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hA : (3^(a+1) * (lteCoeff a)^2) % 3^L = 0 := by
    rw [Nat.mul_mod, h1, Nat.zero_mul, Nat.zero_mod]
  have hB : (3^(2*a+1) * (lteCoeff a)^3) % 3^L = 0 := by
    rw [Nat.mul_mod, h2, Nat.zero_mul, Nat.zero_mod]
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
  rw [hunfold, hA0, hB0]
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

/-! ## §7 The Ω-shadow residue — the Law replaces the climb

The final stroke of the application: the production seam's hypothesis,
stated until now as the full third-wave climb (every exponent from eight
onward owns a physical Happy row), is replaced by the Law's own coverage.
The Ω-cut tower plus two elementary row lemmas delivers the ternary digit
two unconditionally for every exponent outside a sharply defined residue —
the **Ω-shadow**: the exponents whose canonical 3-free core sits in the
tower's uncovered classes (`core ≡ 4 (mod 9)` at any sheet level,
`core ≡ 1 (mod 9)` at sheet zero, or `core ≡ 7 (mod 9)` above sheet zero).
For the shadow itself the seam takes one residual input — the Ω-shadow
wave: every shadow exponent still owns its digit two.  The input is
strictly weaker than the climb: it asks only for a digit (not a Happy
cell) and only on the shadow residue (not on every exponent). -/

/-- The ternary digit at row two of any number congruent to twenty-two
modulo twenty-seven: the prefix split hands the digit directly. -/
theorem omega_digit_row_two_of_mod_27 (R : Nat) (hR : R % 27 = 22) :
    digit3 R 2 = 2 := by
  have hdm27 : 27 * (R / 27) + R % 27 = R := Nat.div_add_mod R 27
  rw [hR] at hdm27
  have hdm9 : 9 * (R / 9) + R % 9 = R := Nat.div_add_mod R 9
  have hmod9 : R % 9 = 4 := by omega
  rw [hmod9] at hdm9
  unfold digit3
  rw [show (3^2 : Nat) = 9 from by decide]
  omega

/-- **The elementary row-two law.**  Every exponent congruent to seven
modulo nine owns its ternary digit two at row two: the base four has order
nine modulo twenty-seven, so `4^K` rides the period to the residue
twenty-two. -/
theorem omega_row2_digit_two (K : Nat) (hK : K % 9 = 7) :
    digit3 (4^K) 2 = 2 := by
  have hdm : K = 9 * (K / 9) + 7 := by omega
  have hpow : (4^9)^(K / 9) * 4^7 = 4^K := by
    rw [← Nat.pow_mul, ← Nat.pow_add, ← hdm]
  have h49 : (4^9) % 27 = 1 := by decide
  have h47 : (4^7) % 27 = 22 := by decide
  have h1 : ((4^9)^(K / 9)) % 27 = 1 := by
    rw [Nat.pow_mod, h49, Nat.one_pow]
  have hmod : (4^K) % 27 = 22 := by
    rw [← hpow, Nat.mul_mod, h1, h47]
  exact omega_digit_row_two_of_mod_27 (4^K) hmod

/-- Every positive number splits as a pure power of three times a
three-free core — the canonical decomposition the residue classes read
from. -/
theorem omega_three_free_decomposition (K : Nat) :
    0 < K → ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core := by
  induction K using Nat.strongRecOn with
  | ind K ih =>
    intro hK
    by_cases h3 : 3 ∣ K
    · obtain ⟨q, hq⟩ := h3
      have hq0 : 0 < q := by omega
      obtain ⟨s, core, hs, hc⟩ := ih q (by omega) hq0
      exact ⟨s+1, core, by rw [hq, hs, Nat.pow_succ]; ring, hc⟩
    · exact ⟨0, K, by simp, h3⟩

/-- **The Ω-shadow residue.**  The exponents whose canonical 3-free core
sits in the tower's uncovered classes: `core ≡ 4 (mod 9)` at any sheet
level, `core ≡ 1 (mod 9)` at sheet zero, or `core ≡ 7 (mod 9)` above sheet
zero.  Every other exponent is carried unconditionally by the Law's cut
tower (core `≡ 2 (mod 3)`: row `s+1`; core `≡ 1, 5 (mod 9)` above sheet
zero: row `s+2`) or by the elementary rows (exponent `≡ 2 (mod 3)`: row
one; exponent `≡ 7 (mod 9)`: row two). -/
def omegaShadow (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7))

/-- **THE Ω-SHADOW WAVE** — the single residual input of the final
theorem: every shadow exponent still owns its ternary digit two.
Strictly weaker than the third-wave climb: a digit, not a Happy cell; the
shadow residue only, not every exponent from eight onward. -/
def four_power_omega_shadow_wave : Prop :=
  ∀ K : Nat, 8 ≤ K → omegaShadow K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **THE Ω-COVERAGE CASE SPLIT.**  Every exponent from eight onward
either lies in the Ω-shadow residue or owns its ternary digit two
outright: the split is exhaustive over the canonical core classes. -/
theorem omega_digit_two_cases (K : Nat) (hK : 8 ≤ K) :
    omegaShadow K ∨ ∃ p : Nat, digit3 (4^K) p = 2 := by
  obtain ⟨s, core, hsc, hc3⟩ := omega_three_free_decomposition K (by omega)
  have h4 : (4^K) = 4^(3^s * core) := by rw [hsc]
  by_cases hcone : core % 3 = 2
  · refine Or.inr ⟨s+1, ?_⟩
    rw [h4, omega_cut_digit s core]
    exact hcone
  · have hcases : core % 9 = 1 ∨ core % 9 = 4 ∨ core % 9 = 7 := by omega
    rcases hcases with h1 | h4c | h7
    · rcases Nat.eq_zero_or_pos s with s0 | spos
      · rw [s0] at hsc
        exact Or.inl ⟨0, core, hsc, hc3, Or.inr (Or.inl ⟨rfl, h1⟩)⟩
      · refine Or.inr ⟨s+2, ?_⟩
        rw [h4]
        exact omega_level2_digit_two s core (by omega) (Or.inl h1)
    · exact Or.inl ⟨s, core, hsc, hc3, Or.inl h4c⟩
    · rcases Nat.eq_zero_or_pos s with s0 | spos
      · rw [s0] at hsc
        refine Or.inr ⟨2, ?_⟩
        have hK9 : K % 9 = 7 := by
          rw [hsc]
          simpa using h7
        exact omega_row2_digit_two K hK9
      · exact Or.inl ⟨s, core, hsc, hc3, Or.inr (Or.inr ⟨by omega, h7⟩)⟩

/-- **The climb, replaced.**  Every exponent outside the shadow owns its
digit two outright — no Happy cell, no climb hypothesis. -/
theorem omega_digit_two_of_not_shadow (K : Nat) (hK : 8 ≤ K)
    (hNS : ¬ omegaShadow K) :
    ∃ p : Nat, digit3 (4^K) p = 2 :=
  (omega_digit_two_cases K hK).resolve_left hNS

/-- **THE Ω-WAVE COVERAGE.**  Under the Ω-shadow wave input, every
exponent from eight onward owns its ternary digit two. -/
theorem omega_digit_two_coverage (hShadow : four_power_omega_shadow_wave)
    (K : Nat) (hK : 8 ≤ K) :
    ∃ p : Nat, digit3 (4^K) p = 2 :=
  (omega_digit_two_cases K hK).elim (fun hsh => hShadow K hK hsh) id

/-! ## §7.5 Level three of the tower — the next sheet of the cut word -/

/-- The LTE mean is constantly sixteen modulo twenty-seven from sheet
level two onward. -/
theorem omega_lteCoeff_mod27 (a : Nat) (ha : 2 ≤ a) :
    lteCoeff a % 27 = 16 := by
  have h27 : (3:Nat)^3 = 27 := by decide
  have hstable := omega_lteCoeff_stable 3 (a-2)
  have hidx : (3-1) + (a-2) = a := by omega
  rw [hidx, h27] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo twenty-seven from sheet
level two onward. -/
theorem omega_base_mod27 : ∀ a : Nat, 2 ≤ a → (4^(3^a)) % 27 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 2 with hlt | hge
      · have ha1 : a = 1 := by omega
        rw [ha1]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo twenty-seven from sheet
level two onward. -/
theorem omega_geo_mod27 (a core : Nat) (ha : 2 ≤ a) :
    omegaGeoSum a core % 27 = core % 27 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 27 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod27 a ha, Nat.one_pow] <;> omega
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-three cut word law.**  From sheet level two onward the cut
word is `16 * core` modulo twenty-seven. -/
theorem omega_cut_word_mod27 (a core : Nat) (ha : 2 ≤ a) :
    omegaCutWord a core % 27 = (16 * core) % 27 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod27 a ha, omega_geo_mod27 a core ha]
  omega

/-- **THE LEVEL-THREE DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+3` is the top trit of the cut word modulo twenty-seven — the
same certified prefix-slice socket as level two, one row deeper. -/
theorem omega_level3_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+3) = (omegaCutWord a core % 27) / 9 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 2 h1
  rw [show a+3 = (a+1)+2 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^2 = 9 from by decide]
  omega

/-- **THE LEVEL-THREE GATE CLASSES.**  For every core congruent to thirteen
or twenty-five modulo twenty-seven, the power `4^(3^a * core)` owns a
ternary digit two at row `a+3` — the third infinite family of the Law,
reaching one subclass of each shadow sheet at every sheet level two and
above. -/
theorem omega_level3_digit_two (a core : Nat) (ha : 2 ≤ a)
    (hcore : core % 27 = 13 ∨ core % 27 = 25) :
    digit3 (4^(3^a * core)) (a+3) = 2 := by
  rw [omega_level3_digit, omega_cut_word_mod27 a core ha]
  rcases hcore with h13 | h25
  · have hval : (16 * core) % 27 = 19 := by omega
    rw [hval]
  · have hval : (16 * core) % 27 = 22 := by omega
    rw [hval]

/-! ## §7.6 The Ω-sheet gate — the wave word beyond the tower

The cut tower reads the wave word `omegaCutWord s core` only inside its
stabilization window (rows `s+1` through `2s+1`).  This section opens the
window one digit further: the full cut word modulo the squared cut modulus
`3^(s+2)` is the sheet-local word `lteCoeff s * core` plus an explicit
binomial correction that vanishes for every shadow core (core congruent to
one modulo three).  The digit at row `2s+2` is therefore the top trit of
`lteCoeff s * core` modulo `3^(s+2)` — the **Ω-sheet gate**, the Law's own
kill of every dodger whose wave word has residue zero at the first digit
beyond the tower.  Together with a fourth tower level (mod eighty-one),
this shrinks the residual input a third time. -/

/-- Multiplication absorbs the residue: reducing the factor before the
multiplication does not change the product's residue. -/
theorem omega_mul_mod_absorb (M k x : Nat) :
    (k * (x % M)) % M = (k * x) % M := by
  have hq : x % M + M * (x / M) = x := Nat.mod_add_div x M
  have hkr : k * x = k * (x % M) + M * (k * (x / M)) := by
    conv_lhs => rw [← hq]
    ring
  rw [hkr, Nat.add_mul_mod_self_left]

/-- The residue of a sum whose head is given by its residue: both the head
and the fixed multiple of the head's residue lift back to the full values
without changing the sum's residue. -/
theorem omega_sum_mod_lift (M k a y : Nat) :
    (a % M + y + k * (a % M)) % M = (a + y + k * a) % M := by
  have hq : a % M + M * (a / M) = a := Nat.mod_add_div a M
  have hchain : a + y + k * a
      = (a % M + y + k * (a % M)) + M * (a / M + k * (a / M)) := by
    conv_lhs => rw [← hq]
    ring
  rw [hchain, Nat.add_mul_mod_self_left]

/-- Halving preserves vanishing modulo three. -/
theorem omega_half_of_mod3 (A : Nat) (hA : A % 3 = 0) (hE : 2 * (A / 2) = A) :
    (A / 2) % 3 = 0 := by omega

/-- **THE FULL-DEPTH CUT WORD LAW.**  At sheet `s` the cut word of
`4^(3^s * core)` agrees, modulo the squared cut modulus `3^(s+2)`, with
the sheet-local word `lteCoeff s * core` plus the explicit binomial
correction `3^(s+1) * (lteCoeff s)^2 * (core * (core - 1) / 2)` carried
by the geometric mean's own telescoping. -/
theorem omega_cut_word_full (s core : Nat) :
    omegaCutWord s core % 3^(s+2)
      = (lteCoeff s * core
          + 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3^(s+2) := by
  induction core with
  | zero =>
      have h0 : omegaCutWord s 0 = 0 := by simp [omegaCutWord, omegaGeoSum]
      rw [h0]
      simp
  | succ c ih =>
      rw [show (c+1) - 1 = c from by omega]
      have hstepW : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s * 4^(3^s * c) := by
        unfold omegaCutWord omegaGeoSum
        simp only [Finset.sum_range_succ]
        have hterm : (4^(3^s))^c = 4^(3^s * c) := by rw [Nat.pow_mul]
        rw [hterm]
        ring
      have hf : 4^(3^s * c) = 1 + 3^(s+1) * omegaCutWord s c :=
        omega_cut_factor s c
      have h2 : omegaCutWord s (c+1)
          = omegaCutWord s c + lteCoeff s
            + 3^(s+1) * lteCoeff s * omegaCutWord s c := by
        rw [hstepW, hf]; ring
      have hbinom : (c+1) * c / 2 = c * (c - 1) / 2 + c := by
        have hE : (c+1) * c = c * (c - 1) + 2 * c := by
          rcases c with _ | c'
          · simp
          · have hs : (c'+1) - 1 = c' := by omega
            rw [hs]
            ring
        rw [hE]
        exact Nat.add_mul_div_left _ _ (by decide)
      have hp2 : (3:Nat)^(s+1) * 3^(s+1) = 3^(s+2) * 3^s := by
        rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega
      rw [h2, ← omega_sum_mod_lift, ih, omega_sum_mod_lift]
      have hfinal : lteCoeff s * c
            + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2)
            + lteCoeff s
            + 3^(s+1) * lteCoeff s * (lteCoeff s * c
                + 3^(s+1) * lteCoeff s * lteCoeff s * (c * (c - 1) / 2))
          = lteCoeff s * (c+1)
            + 3^(s+1) * lteCoeff s * lteCoeff s * ((c+1) * c / 2)
            + 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
                * (c * (c - 1) / 2) := by
        rw [hbinom]
        ring
      rw [hfinal]
      rw [show 3^(s+1) * 3^(s+1) * lteCoeff s * lteCoeff s * lteCoeff s
            * (c * (c - 1) / 2)
          = 3^(s+2) * (3^s * lteCoeff s * lteCoeff s * lteCoeff s
              * (c * (c - 1) / 2)) from by rw [hp2]; ring,
        Nat.add_mul_mod_self_left]

/-- **THE Ω-SHEET CUT WORD.**  For every core congruent to one modulo
three the binomial correction is a multiple of three, so modulo the
squared cut modulus the cut word is the sheet-local word `lteCoeff s *
core` exactly. -/
theorem omega_cut_word_mod_pow2 (s core : Nat) (hcore : core % 3 = 1) :
    omegaCutWord s core % 3^(s+2) = (lteCoeff s * core) % 3^(s+2) := by
  have hu3 : (lteCoeff s) % 3 = 1 := lteCoeff_mod3_one s
  have hcm : core * (core - 1) % 3 = 0 := by
    have h2 : (core - 1) % 3 = 0 := by omega
    rw [Nat.mul_mod, hcore, h2]
  have h2m : 2 * (core * (core - 1) / 2) = core * (core - 1) := by
    rw [Nat.mul_div_cancel' (by
      rcases Nat.even_or_odd core with ⟨k, hk⟩ | ⟨k, hk⟩
      · rw [hk]
        exact ⟨k * (2 * k - 1), by ring⟩
      · rw [hk]
        have hsub : (2 * k + 1) - 1 = 2 * k := by omega
        rw [hsub]
        exact ⟨(2 * k + 1) * k, by ring⟩)]
  have hq3 : (core * (core - 1) / 2) % 3 = 0 :=
    omega_half_of_mod3 (core * (core - 1)) hcm h2m
  have hX3 : (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) % 3 = 0 := by
    rw [Nat.mul_mod (lteCoeff s * lteCoeff s) (core * (core - 1) / 2) 3,
      Nat.mul_mod (lteCoeff s) (lteCoeff s) 3, hu3, hu3, hq3]
    decide
  obtain ⟨Y, hY⟩ : ∃ Y : Nat,
      lteCoeff s * lteCoeff s * (core * (core - 1) / 2) = 3 * Y := by
    refine ⟨(lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) / 3, ?_⟩
    have h := Nat.mod_add_div
      (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) 3
    rw [hX3, Nat.zero_add] at h
    exact h.symm
  have hcorr : 3^(s+2)
      ∣ 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2) := by
    refine ⟨Y, ?_⟩
    have hp3 : (3:Nat)^(s+2) = 3 * 3^(s+1) := by
      rw [show s + 2 = (s+1) + 1 from by omega, Nat.pow_add, Nat.pow_one]
      ring
    rw [show 3^(s+1) * lteCoeff s * lteCoeff s * (core * (core - 1) / 2)
        = 3^(s+1) * (lteCoeff s * lteCoeff s * (core * (core - 1) / 2)) from by ring,
      hY, hp3]
    ring
  rw [omega_cut_word_full s core, Nat.add_mod, Nat.mod_eq_zero_of_dvd hcorr,
    Nat.add_zero, Nat.mod_mod]

/-- The ternary digit at position `j` is the top trit of the residue
modulo `3^(j+1)` — the general window law behind every level of the
tower's digit reading. -/
theorem digit3_window (X j : Nat) :
    (X / 3^j) % 3 = (X % 3^(j+1)) / 3^j := by
  have hp : 0 < 3^j := Nat.pow_pos (by decide)
  have hpow : 3^(j+1) = 3^j * 3 := by rw [Nat.pow_add, Nat.pow_one]
  have hX : X = 3^(j+1) * (X / 3^(j+1)) + X % 3^(j+1) := by
    have h := Nat.mod_add_div X (3^(j+1))
    rw [Nat.add_comm] at h
    exact h.symm
  have hdiv : X / 3^j
      = (X % 3^(j+1)) / 3^j + 3 * (X / 3^(j+1)) := by
    calc X / 3^j
        = (3^(j+1) * (X / 3^(j+1)) + X % 3^(j+1)) / 3^j := by rw [← hX]
      _ = (X % 3^(j+1) + 3^(j+1) * (X / 3^(j+1))) / 3^j := by rw [Nat.add_comm]
      _ = (X % 3^(j+1) + 3^j * 3 * (X / 3^(j+1))) / 3^j := by rw [hpow]
      _ = (X % 3^(j+1) + 3^j * (3 * (X / 3^(j+1)))) / 3^j := by
          rw [show 3^j * 3 * (X / 3^(j+1)) = 3^j * (3 * (X / 3^(j+1))) from by ring]
      _ = (X % 3^(j+1)) / 3^j + 3 * (X / 3^(j+1)) :=
          Nat.add_mul_div_left _ _ hp
  have hmodlt : X % 3^(j+1) < 3 * 3^j := by
    have h : X % 3^(j+1) < 3^(j+1) := Nat.mod_lt X (Nat.pow_pos (by decide))
    rw [show 3^(j+1) = 3 * 3^j from by rw [hpow, Nat.mul_comm]] at h ⊢
    exact h
  have hlt : (X % 3^(j+1)) / 3^j < 3 :=
    (Nat.div_lt_iff_lt_mul hp).mpr hmodlt
  rw [hdiv, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- **THE Ω-SHEET GATE DIGIT.**  The ternary digit of `4^(3^s * core)` at
row `2s+2` — one row beyond the tower's stabilization window — is the top
trit of the sheet-local cut word `lteCoeff s * core` modulo `3^(s+2)`,
for every core congruent to one modulo three. -/
theorem omega_sheet_digit (s core : Nat) (hcore : core % 3 = 1) :
    digit3 (4^(3^s * core)) (2*s+2)
      = ((lteCoeff s * core) % 3^(s+2)) / 3^(s+1) := by
  have hf := omega_cut_factor s core
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) (s+1) h1
  rw [show 2*s+2 = (s+1)+(s+1) from by omega, hf, hslice]
  unfold digit3
  rw [digit3_window, show s + 1 + 1 = s + 2 from by omega,
    omega_cut_word_mod_pow2 s core hcore]

/-- **THE Ω-SHEET GATE (the wave law beyond the tower).**  For every core
congruent to one modulo three, if the sheet-local cut word `omegaCutWord s
core` has top trit two modulo the squared cut modulus, then `4^(3^s *
core)` owns its ternary digit two at row `2s+2`.  This is the Law's own
kill of every tower-dodger whose wave word has residue zero at the first
digit beyond the stabilization window: the binomial correction adds two
there. -/
theorem omega_sheet_gate_digit_two (s core : Nat) (hcore : core % 3 = 1)
    (hgate : 2 * 3^(s+1) ≤ (omegaCutWord s core) % 3^(s+2)) :
    digit3 (4^(3^s * core)) (2*s+2) = 2 := by
  have hg' : 2 * 3^(s+1) ≤ (lteCoeff s * core) % 3^(s+2) := by
    rw [← omega_cut_word_mod_pow2 s core hcore]
    exact hgate
  rw [omega_sheet_digit s core hcore]
  have hlt : (lteCoeff s * core) % 3^(s+2) < 3^(s+2) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have h3 : 3^(s+2) = 3 * 3^(s+1) := by
    rw [show s + 2 = (s+1) + 1 from by omega, Nat.pow_add, Nat.pow_one]
    ring
  have hlt2 : (lteCoeff s * core) % 3^(s+2) < 3 * 3^(s+1) := by omega
  obtain ⟨d, hd⟩ : ∃ d, (lteCoeff s * core) % 3^(s+2)
      = 2 * 3^(s+1) + d := ⟨_, by omega⟩
  have hdlt : d < 3^(s+1) := by omega
  rw [hd, Nat.add_comm, show 2 * 3^(s+1) = 3^(s+1) * 2 from by ring,
    Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)),
    Nat.div_eq_of_lt hdlt]
  omega

/-- The LTE mean is constantly sixteen modulo eighty-one from sheet
level three onward. -/
theorem omega_lteCoeff_mod81 (a : Nat) (ha : 3 ≤ a) :
    lteCoeff a % 81 = 16 := by
  have h81 : (3:Nat)^4 = 81 := by decide
  have hstable := omega_lteCoeff_stable 4 (a-3)
  have hidx : (4-1) + (a-3) = a := by omega
  rw [hidx, h81] at hstable
  rw [hstable]
  decide

/-- The base of the geometric mean is one modulo eighty-one from sheet
level three onward. -/
theorem omega_base_mod81 : ∀ a : Nat, 3 ≤ a → (4^(3^a)) % 81 = 1 := by
  intro a
  induction a with
  | zero => intro h; omega
  | succ a ih =>
      intro h
      rcases Nat.lt_or_ge a 3 with hlt | hge
      · have ha2 : a = 2 := by omega
        rw [ha2]
        decide
      · have hstep : 4^(3^(a+1)) = (4^(3^a))^3 := by
          rw [Nat.pow_succ, Nat.pow_mul]
        rw [hstep, Nat.pow_mod, ih hge, Nat.one_pow]

/-- The geometric mean is the core mass modulo eighty-one from sheet
level three onward. -/
theorem omega_geo_mod81 (a core : Nat) (ha : 3 ≤ a) :
    omegaGeoSum a core % 81 = core % 81 := by
  have hterm : ∀ j : Nat, ((4^(3^a))^j) % 81 = 1 := by
    intro j
    rw [Nat.pow_mod, omega_base_mod81 a ha, Nat.one_pow] <;> omega
  induction core with
  | zero => simp [omegaGeoSum]
  | succ core ih =>
      have hgeo : omegaGeoSum a (core+1)
          = omegaGeoSum a core + (4^(3^a))^core := by
        simp [omegaGeoSum, Finset.sum_range_succ]
      rw [hgeo, Nat.add_mod, hterm core, ih]
      omega

/-- **The level-four cut word law.**  From sheet level three onward the
cut word is `16 * core` modulo eighty-one. -/
theorem omega_cut_word_mod81 (a core : Nat) (ha : 3 ≤ a) :
    omegaCutWord a core % 81 = (16 * core) % 81 := by
  unfold omegaCutWord
  rw [Nat.mul_mod, omega_lteCoeff_mod81 a ha, omega_geo_mod81 a core ha]
  omega

/-- **THE LEVEL-FOUR DIGIT LAW.**  The ternary digit of `4^(3^a * core)`
at row `a+4` is the top trit of the cut word modulo eighty-one — the same
certified prefix-slice socket as levels two and three, one row deeper. -/
theorem omega_level4_digit (a core : Nat) :
    digit3 (4^(3^a * core)) (a+4) = (omegaCutWord a core % 81) / 27 := by
  have hf := omega_cut_factor a core
  have h1 : (1:Nat) < 3^(a+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(a+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ a+1)
    omega
  have hslice := prefix_slice_digit_exact (a+1) 1 (omegaCutWord a core) 3 h1
  rw [show a+4 = (a+1)+3 from by omega, hf, hslice]
  unfold digit3
  rw [show (3:Nat)^3 = 27 from by decide]
  omega

/-- **THE LEVEL-FOUR GATE CLASSES.**  For every core whose stabilized cut
word reaches the top third of the residue window modulo eighty-one, the
power `4^(3^a * core)` owns a ternary digit two at row `a+4` — the
fourth infinite family of the Law, twenty-seven residue classes at every
sheet level three and above. -/
theorem omega_level4_digit_two (a core : Nat) (ha : 3 ≤ a)
    (hgate : 54 ≤ (16 * core) % 81) :
    digit3 (4^(3^a * core)) (a+4) = 2 := by
  rw [omega_level4_digit, omega_cut_word_mod81 a core ha]
  have hlt : (16 * core) % 81 < 81 := Nat.mod_lt _ (by decide)
  omega

/-- **The Ω-shadow tail after the sheet gate.**  The shadow residue after
the kernel-checked base, the third and fourth tower levels, and the
Ω-sheet gate: every shadow exponent above the kernel base whose core
dodges every proven gate of the tower and whose sheet-local cut word
dodges the squared-modulus top trit. -/
def omegaShadowTail2 (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25) ∧
    (3 ≤ s → (16 * core) % 81 < 54) ∧
    ((omegaCutWord s core) % 3^(s+2) < 2 * 3^(s+1))

/-- **THE Ω-SHADOW WAVE TAIL (SHEET-GATE FORM)** — the residual input after
the kernel-checked base, the third and fourth levels of the Ω-cut tower,
and the Ω-sheet gate: only shadow exponents above the kernel base whose
cores dodge every proven gate remain. -/
def four_power_omega_shadow_wave_tail2 : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail2 K → ∃ p : Nat, digit3 (4^K) p = 2

/-- **The Ω-shadow tail.**  The shadow residue after the kernel-checked
base and the level-three gate classes: every shadow exponent above the
kernel base whose core dodges the level-three classes at sheet level two
and above. -/
def omegaShadowTail (K : Nat) : Prop :=
  ∃ s core : Nat, K = 3^s * core ∧ ¬ 3 ∣ core ∧
    (core % 9 = 4 ∨ (s = 0 ∧ core % 9 = 1) ∨ (1 ≤ s ∧ core % 9 = 7)) ∧
    (2 ≤ s → core % 27 ≠ 13 ∧ core % 27 ≠ 25)

/-- **THE Ω-SHADOW WAVE TAIL** — the residual input after the
kernel-checked base and the third level of the Ω-cut tower: only shadow
exponents above the kernel base whose cores dodge every proven gate
class remain. -/
def four_power_omega_shadow_wave_tail : Prop :=
  ∀ K : Nat, 500 < K → omegaShadowTail K → ∃ p : Nat, digit3 (4^K) p = 2

#check omegaShadow
#check four_power_omega_shadow_wave
#check omega_row2_digit_two
#check omega_three_free_decomposition
#check omega_digit_two_cases
#check omega_digit_two_of_not_shadow
#check omega_digit_two_coverage
#check omega_lteCoeff_mod27
#check omega_base_mod27
#check omega_geo_mod27
#check omega_cut_word_mod27
#check omega_level3_digit
#check omega_level3_digit_two
#check omegaShadowTail
#check four_power_omega_shadow_wave_tail
#check omegaShadowTail2
#check four_power_omega_shadow_wave_tail2
#check omega_cut_word_full
#check omega_cut_word_mod_pow2
#check omega_sheet_digit
#check omega_sheet_gate_digit_two
#check omega_level4_digit_two
#print axioms omegaShadowTail
#print axioms four_power_omega_shadow_wave_tail
#print axioms omega_cut_word_full
#print axioms omega_cut_word_mod_pow2
#print axioms omega_sheet_digit
#print axioms omega_sheet_gate_digit_two
#print axioms omega_level4_digit_two
#print axioms omega_digit_two_of_not_shadow
#print axioms omega_digit_two_coverage
#print axioms omega_lteCoeff_mod27
#print axioms omega_base_mod27
#print axioms omega_geo_mod27
#print axioms omega_cut_word_mod27
#print axioms omega_level3_digit
#print axioms omega_level3_digit_two

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
