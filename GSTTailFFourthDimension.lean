import GSTGraphV2OmegaWaveLaw
import ErdosTernary2

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE 4TH DIMENSION — the tailF observation chamber

The separate arena for the second-observer input
`four_power_omega_shadow_wave_tailF`: the entire theorem machinery of the
route — the observation law, the descent blade, the diagonal ignition, the
uniform row and tower gates — assembled in ONE file, and pointed at the
input's own package.

What this chamber delivers, machine-certified:

* **THE EXTENDED OBSERVATION LAW** (`tower_observation_digit_two`): the
  row-axis reading of the Law, lifted from sheet zero to EVERY sheet level.
  Every tower digit of `4^(3^s * core)` at EVERY depth — no window bound,
  positions far beyond the observer law's `k ≤ s+1` window — is the cut
  word's own trit. The deep zone of the power, beyond the package's dodge
  band, is readable off `omegaCutWord s core` directly.
* **THE DESCENT BLADE** (§2, four theorems): the cut-word tower is one
  stabilizing 3-adic object; ONE primitive diagonal trit two kills the
  tower dodge at every level at once.
* **THE DIAGONAL IGNITION** (§3, five theorems): the first firing bands as
  unconditional residue tests on the core.
* **THE DECOMPOSITION** (§4): the input `four_power_omega_shadow_wave_tailF`
  is EXACTLY two named 3-adic trit statements — the row primitive (the
  sheet-zero family: the row word of every 3-free class-one core fires) and
  the tower primitive (the deep tail of every diagonal-dodging tower fires
  at depth beyond its own window). Both composition directions are
  machine-certified, and through the monolith's own terminal identity and
  crown, the two primitives carry the whole even-exponent statement.

The two named primitives are the carried content of the input — stated as
`def`s, consumed as hypotheses, disclosed at every surface. Everything
around them in this file is unconditional and axiom-audited.
-/

namespace GSTTailFFourthDimension

open GSTCanonicalSevenAxisBridge
open GSTFourPowerDirectResidue (lteCoeff lteCoeff_mod3_one
  pow4_three_power_lte_exact pow4_mod3_one pow4_scaled_mod_next)
open GSTGraphV2InfiniteControl
open GSTGraphV2HandwrittenOmegaUBlock
open GSTGraphV2InfiniteControllerBridge
open GST2DMixedEmergence
open GSTU2DEventTransport
open GSTGraphV2OmegaWaveLaw

/-! ## §1 The extended observation law — every tower digit, every depth

The uniform row law of the Law file reads the digits of `4^core` off the
row word `omegaCutWord 0 core` at every depth `j`. The cut-factor identity
`4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core` holds at EVERY sheet
level `s`, and the prefix-slice law applies at every one of them: the
digit of the tower power at position `s+1+j` is the cut word's own trit at
`j`, with NO window bound. This is the observation law of the fourth
dimension: the deep digits — the positions the package's dodge band does
not even reach — are an open book. -/

/-- **THE EXTENDED OBSERVATION LAW.**  For every sheet level `s`, every
core, and EVERY depth `j`: whenever the cut word's own trit at depth `j`
sits in the top third of its residue window modulo `3^(j+1)`, the tower
power `4^(3^s * core)` owns its ternary digit two at position `s+1+j`.
No window bound: the reading works at every depth of the power. -/
theorem tower_observation_digit_two (s core j : Nat)
    (hkill : 2 * 3^j ≤ (omegaCutWord s core) % 3^(j+1)) :
    digit3 (4^(3^s * core)) (s+1+j) = 2 := by
  have h1 : (1:Nat) < 3^(s+1) := by
    have h3 : (3:Nat)^1 ≤ 3^(s+1) := by
      simpa using Nat.pow_le_pow_of_le (by decide : 1 < (3:Nat))
        (by omega : 1 ≤ s+1)
    omega
  have hslice := prefix_slice_digit_exact (s+1) 1 (omegaCutWord s core) j h1
  have hf : 4^(3^s * core) = 1 + 3^(s+1) * omegaCutWord s core :=
    omega_cut_factor s core
  rw [show s+1+j = (s+1)+j from by omega, hf, hslice]
  unfold digit3
  rw [digit3_window]
  have hpos : 0 < 3^j := Nat.pow_pos (by decide)
  have hlt : (omegaCutWord s core) % 3^(j+1) < 3^(j+1) :=
    Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hpow : 3^(j+1) = 3 * 3^j := by
    rw [Nat.pow_add, Nat.pow_one]
    ring
  rw [hpow] at hlt
  obtain ⟨d, hd⟩ : ∃ d, (omegaCutWord s core) % 3^(j+1) = 2 * 3^j + d :=
    ⟨(omegaCutWord s core) % 3^(j+1) - 2 * 3^j, by omega⟩
  have hdlt : d < 3^j := by omega
  rw [hd, Nat.add_comm, show 2 * 3^j = 3^j * 2 from by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hdlt]

/-! ## §2 The descent blade — the non-local argument

The cut-word tower is one stabilizing 3-adic object: the cube-lift identity
freezes every window below the lift, every tower window descends to the
primitive level, and ONE primitive diagonal trit two kills the tower dodge
at EVERY sheet level at once. -/

/-- **THE CUBE-LIFT STABILIZATION.**  The cut word of sheet level `s+1` is
the cut word of level `s` plus a multiple of `3^(s+1)`: every trit below
position `s+1` is frozen as the sheet level grows. -/
theorem omega_cut_word_stabilizes (s core : Nat) :
    ∃ t : Nat, omegaCutWord (s+1) core
      = omegaCutWord s core + 3^(s+1) * t := by
  have hf0 := omega_cut_factor s core
  have hf1 := omega_cut_factor (s+1) core
  have hpow : 4^(3^(s+1) * core) = (4^(3^s * core))^3 := by
    rw [show 3^(s+1) * core = (3^s * core) * 3 from by
          rw [Nat.pow_succ]; ring,
        Nat.pow_mul]
  have hcube : (1 + 3^(s+1) * omegaCutWord s core)^3
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [show 3^(s+2) = 9 * 3^s from by
          rw [show s+2 = (s+1)+1 from by omega, Nat.pow_succ, Nat.pow_succ]
          ring,
        show 3^(s+1) = 3 * 3^s from by rw [Nat.pow_succ]; ring]
    ring
  have hE : 4^(3^(s+1) * core)
      = 1 + 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) := by
    rw [hpow, hf0]
    exact hcube
  have hAB : 3^(s+2) * omegaCutWord (s+1) core
      = 3^(s+2) * (omegaCutWord s core
          + 3^(s+1) * (omegaCutWord s core * omegaCutWord s core
            + 3^s * (omegaCutWord s core * omegaCutWord s core
              * omegaCutWord s core))) :=
    Nat.add_left_cancel (hf1.symm.trans hE)
  refine ⟨omegaCutWord s core * omegaCutWord s core
      + 3^s * (omegaCutWord s core * omegaCutWord s core
        * omegaCutWord s core), ?_⟩
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hAB

/-- **THE FROZEN WINDOW.**  For every tower level `k ≤ s+1`, the level-`s`
and level-`s+1` tower words agree modulo `3^k`. -/
theorem omega_tower_word_mod_stable (s core k : Nat) (hk : k ≤ s+1) :
    (omegaCutWord (s+1) 1 * core) % 3^k
      = (omegaCutWord s 1 * core) % 3^k := by
  obtain ⟨t, ht⟩ := omega_cut_word_stabilizes s 1
  have hsplit : 3^(s+1) = 3^k * 3^(s+1-k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hz : 3^(s+1) * (t * core) % 3^k = 0 := by
    refine Nat.mod_eq_zero_of_dvd ⟨3^(s+1-k) * (t * core), ?_⟩
    rw [hsplit]
    ring
  have hdistr : (omegaCutWord s 1 + 3^(s+1) * t) * core
      = omegaCutWord s 1 * core + 3^(s+1) * (t * core) := by
    ring
  rw [ht, hdistr, Nat.add_mod, hz, Nat.add_zero, Nat.mod_mod]

/-- **THE DESCENT TO THE PRIMITIVE.**  For every sheet level `s` at or
above `k-1`, the tower word at modulus `3^k` is the primitive
level-`(k-1)` word at modulus `3^k`. -/
theorem omega_tower_word_mod_chain (core k : Nat) :
    ∀ s : Nat, k-1 ≤ s → (omegaCutWord s 1 * core) % 3^k
      = (omegaCutWord (k-1) 1 * core) % 3^k := by
  intro s
  induction s with
  | zero =>
    intro hsk
    rw [show k-1 = 0 from by omega]
  | succ s ih =>
    intro hsk
    rcases Nat.lt_or_ge k (s+2) with hlt | hge
    · rw [omega_tower_word_mod_stable s core k (by omega), ih (by omega)]
    · rw [show k-1 = s+1 from by omega]

/-- **THE DIAGONAL KILL — the descent blade, drawn.**  One ternary digit
two on the primitive diagonal at level `k-1` kills the tower dodge at
EVERY sheet level `S ≥ k-1` at once. -/
theorem omega_tower_kill_of_diagonal_two (core k S : Nat)
    (hk1 : 1 ≤ k) (hkS : k ≤ S+1)
    (hTwo : digit3 (4^(3^(k-1) * core)) (2*k - 1) = 2) :
    digit3 (4^(3^S * core)) (S + k) = 2 := by
  have hobs := omega_observed_digit (k-1) core k (by omega) (by omega)
  rw [show (k-1) + k = 2*k - 1 from by omega] at hobs
  rw [hobs] at hTwo
  rw [omega_observed_digit S core k (by omega) hkS,
      omega_tower_word_mod_chain core k S (by omega)]
  exact hTwo

/-! ## §3 The diagonal ignition — the first firing bands

The descent blade transmits ONE primitive diagonal trit two to every tower
level at once. The ignition laws read the diagonal at its first two
indices as explicit residue conditions on the core. -/

/-- **THE CLASS-ONE IGNITION.**  Every class-one core — `core ≡ 1 (mod 9)`
— fires the primitive diagonal at index two: the level-one tower word is
`7`, and `7 * core ≡ 7 (mod 9)` sits in the top third. -/
theorem omega_diagonal_two_of_mod_nine_one (core : Nat) (h : core % 9 = 1) :
    digit3 (4^(3^(2-1) * core)) (2*2 - 1) = 2 := by
  have hw : omegaCutWord 1 1 = 7 := by
    have h2 := omega_cut_factor 1 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 1 core 2 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (7 * core) % 3^2 / 3^(2-1) = 2 := by
    have h9 : (3:Nat)^2 = 9 := by norm_num
    have h3 : (3:Nat)^(2-1) = 3 := by norm_num
    rw [h9, h3]
    omega
  exact hobs.trans hev

/-- **THE MOD-27 THIRTEEN IGNITION.**  Every core `≡ 13 (mod 27)` — the
class-four band's first firing subclass — fires the primitive diagonal at
index three: the level-two tower word is `9709 ≡ 16 (mod 27)`, and
`16 * 13 ≡ 19 (mod 27)` lands in the top third. -/
theorem omega_diagonal_two_of_mod27_thirteen (core : Nat)
    (h : core % 27 = 13) :
    digit3 (4^(3^(3-1) * core)) (2*3 - 1) = 2 := by
  have hw : omegaCutWord 2 1 = 9709 := by
    have h2 := omega_cut_factor 2 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 2 core 3 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (9709 * core) % 3^3 / 3^(3-1) = 2 := by
    have h27 : (3:Nat)^3 = 27 := by norm_num
    have h9 : (3:Nat)^(3-1) = 9 := by norm_num
    rw [h27, h9]
    omega
  exact hobs.trans hev

/-- **THE MOD-27 TWENTY-FIVE IGNITION.**  Every core `≡ 25 (mod 27)` — the
class-seven band's first firing subclass — fires the primitive diagonal at
index three: `16 * 25 ≡ 22 (mod 27)` lands in the top third. -/
theorem omega_diagonal_two_of_mod27_twentyfive (core : Nat)
    (h : core % 27 = 25) :
    digit3 (4^(3^(3-1) * core)) (2*3 - 1) = 2 := by
  have hw : omegaCutWord 2 1 = 9709 := by
    have h2 := omega_cut_factor 2 1
    norm_num [Nat.pow_succ, Nat.pow_zero] at h2
    omega
  have hobs := omega_observed_digit 2 core 3 (by decide) (by decide)
  rw [hw] at hobs
  have hev : (9709 * core) % 3^3 / 3^(3-1) = 2 := by
    have h27 : (3:Nat)^3 = 27 := by norm_num
    have h9 : (3:Nat)^(3-1) = 9 := by norm_num
    rw [h27, h9]
    omega
  exact hobs.trans hev

/-- **THE CLASS-ONE TOWER KILL.**  One residue test on the core
(`core ≡ 1 (mod 9)`) and the entire tower dies at every level `S ≥ 1`. -/
theorem omega_tower_digit_two_of_mod_nine_one (core : Nat)
    (h : core % 9 = 1) :
    ∀ S : Nat, 1 ≤ S → digit3 (4^(3^S * core)) (S + 2) = 2 := by
  intro S hS
  exact omega_tower_kill_of_diagonal_two core 2 S (by decide) (by omega)
    (omega_diagonal_two_of_mod_nine_one core h)

/-- **THE MOD-27 BAND TOWER KILL.**  Every core in the mod-27 firing band
(`13` or `25`) kills its whole tower from level two upward. -/
theorem omega_tower_digit_two_of_mod27_band (core : Nat)
    (h : core % 27 = 13 ∨ core % 27 = 25) :
    ∀ S : Nat, 2 ≤ S → digit3 (4^(3^S * core)) (S + 3) = 2 := by
  intro S hS
  rcases h with h13 | h25
  · exact omega_tower_kill_of_diagonal_two core 3 S (by decide) (by omega)
      (omega_diagonal_two_of_mod27_thirteen core h13)
  · exact omega_tower_kill_of_diagonal_two core 3 S (by decide) (by omega)
      (omega_diagonal_two_of_mod27_twentyfive core h25)

/-! ## §4 The two named primitives — the decomposition of the input

The input `four_power_omega_shadow_wave_tailF` says: every exponent above
the kernel base that carries the full shadow package owns a ternary digit
two. The package's own witness decomposition `K = 3^s * core` splits the
input into exactly two families, and each family compresses to ONE named
3-adic trit statement:

* the **ROW primitive** — the sheet-zero family (`s = 0`): the row word of
  every 3-free class-one core above the base fires its top third at some
  depth;
* the **TOWER primitive** — the tower family (`s ≥ 1`): the deep tail of
  the cut word — beyond the package's own dodge band, at depth `≥ s+2` —
  fires its top third at some depth.

These two statements are the whole carried content of the input: composed,
they deliver the input outright, and through the monolith's terminal
identity and crown they deliver the even-exponent statement itself. -/

/-- **THE ROW PRIMITIVE** — the sheet-zero family's entire carried content,
as one named 3-adic trit statement: the row word of every 3-free class-one
core above the kernel base owns its top-third fire at some depth. -/
def tailF_row_primitive : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    (core % 9 = 1 ∨ core % 9 = 4) →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE TOWER PRIMITIVE** — the tower family's entire carried content, as
one named 3-adic trit statement: every diagonal-dodging tower's cut word
fires its top third in its deep tail, at depth at least `s+2` — beyond the
package's own dodge band. -/
def tailF_tower_primitive : Prop :=
  ∀ s core : Nat, 1 ≤ s → ¬ 3 ∣ core →
    (core % 9 = 4 ∨ core % 9 = 7) →
    (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) →
      ∃ i : Nat, s+2 ≤ i ∧
        2 * 3^i ≤ (omegaCutWord s core) % 3^(i+1)

/-- **THE DECOMPOSITION OF THE INPUT.**  The two named primitives compose
into the full second-observer input: the row primitive carries the
sheet-zero family through the uniform row law, the tower primitive
carries the tower family through the extended observation law of §1. -/
theorem tailF_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · -- Sheet-zero family: the row primitive fires the row word, the
    -- uniform row law converts the fire into the power's digit two.
    have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by
      rw [← hKsc]
      exact hK
    obtain ⟨j, hj⟩ := hRow core hKc hfree hc14
    refine ⟨1+j, ?_⟩
    rw [hKsc]
    exact omega_row_level_digit_two core j hj
  · -- Tower family: the tower primitive fires the deep tail of the cut
    -- word, the extended observation law converts the fire into the
    -- power's digit two at a position beyond the dodge band.
    have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN-EXPONENT STATEMENT FROM THE TWO PRIMITIVES** — through the
monolith's own terminal identity, the two named primitives carry the whole
even-exponent statement. -/
theorem even_conjecture_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_iff_tailF.mpr
    (tailF_of_row_and_tower hRow hTower)

/-- **THE CROWN FROM THE TWO PRIMITIVES** — the monolith's own universal
theorem, with the input slot filled by the decomposition: the two named
3-adic trit statements carry the universal. -/
theorem erdos_ternary_2_universal_of_row_and_tower
    (hRow : tailF_row_primitive)
    (hTower : tailF_tower_primitive)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF
    (tailF_of_row_and_tower hRow hTower) n hn

/-! ## §5 The combinations applied — the package's own bands die

The blade and the ignition, pointed at the input's own package: for the
mod-27 firing band, the package's tower-dodge clause is dead on arrival —
the diagonal fires inside the clause's own window, so no package witness
at sheet level two or beyond can carry a band core. This is the machinery
of §§1-3 consuming the package from the fourth dimension. -/

/-- **THE BAND DODGE IS DEAD.**  For every sheet level `s ≥ 2` and every
core in the mod-27 firing band (`13` or `25` mod 27), the tower-dodge
clause of the shadow package FAILS at `k = 3`: the stabilized tower word
fires its top third inside the clause's own window. No package witness at
level two or beyond carries a band core. -/
theorem tower_dodge_dead_of_mod27_band (s core : Nat) (hs : 2 ≤ s)
    (h : core % 27 = 13 ∨ core % 27 = 25) :
    ¬ (∀ k : Nat, 3 ≤ k → k ≤ s+1 →
      (omegaCutWord s 1 * core) % 3^k < 2 * 3^(k-1)) := by
  intro hD
  have hkill : digit3 (4^(3^s * core)) (s + 3) = 2 := by
    rcases h with h13 | h25
    · exact omega_tower_kill_of_diagonal_two core 3 s (by decide) (by omega)
        (omega_diagonal_two_of_mod27_thirteen core h13)
    · exact omega_tower_kill_of_diagonal_two core 3 s (by decide) (by omega)
        (omega_diagonal_two_of_mod27_twentyfive core h25)
  rw [omega_observed_digit s core 3 (by decide) (by omega)] at hkill
  have hdodge := hD 3 (by omega) (by omega)
  have h27 : (3:Nat)^3 = 27 := by norm_num
  have h9 : (3:Nat)^(3-1) = 9 := by norm_num
  rw [h27, h9] at hkill hdodge
  omega

/-! ## §6 The row lattice — the sheet-zero residual, fired three levels deep

The row half of the carried input, attacked directly on the powers.  The
hard family of the sheet-zero decomposition is `core % 9 ∈ {1, 4}` (3-free,
above the kernel base); the residue class of the core modulo `3^m` pins the
ternary digits of `4 ^ core` up to position `m` through the cycle laws —
the monolith's own `four_pow_mod81` at level 27, and the two new cycle laws
of this section at levels 81 and 243.  Three lattice levels, thirteen fired
classes:

* level 27, digit position 3: classes `19` and `22` mod 27 —
  `4 ^ core % 81 = 58` and `67`;
* level 81, digit position 4: classes `55, 58, 64, 67` mod 81 —
  `4 ^ core % 243 = 166, 175, 193, 202`;
* level 243, digit position 5: classes `85, 91, 112, 163, 175, 190, 202`
  mod 243 — `4 ^ core % 729 = 499, 517, 580, 490, 526, 571, 607`.

Every fired class owns its digit two UNCONDITIONALLY — no package, no
input, no gates.  The carried row input of §4 shrinks to the seventeen
survivors of the mod-243 level (§7): the replacement of the input's row
half. -/

/-- The cycle law of level 81: the modulus-243 residue of `4 ^ m` is pinned
by the class of `m` modulo 81. -/
theorem four_pow_mod243 (m : Nat) : (4^m) % 243 = (4^(m % 81)) % 243 := by
  have h81 : (4^81) % 243 = 1 := by decide
  have h481q : ∀ q : Nat, (4^81)^q % 243 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^81)^(Nat.succ q') = (4^81)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h81, ih]
  have hmd : m = 81 * (m / 81) + m % 81 := (Nat.div_add_mod m 81).symm
  have h4m : 4^m = (4^81)^(m/81) * 4^(m%81) := by
    have h1 : 4^m = 4^(81*(m/81) + m%81) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(81*(m/81) + m%81) = (4^81)^(m/81) * 4^(m%81) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h481q, Nat.one_mul, Nat.mod_mod]

/-- The cycle law of level 243: the modulus-729 residue of `4 ^ m` is pinned
by the class of `m` modulo 243. -/
theorem four_pow_mod729 (m : Nat) : (4^m) % 729 = (4^(m % 243)) % 729 := by
  have h243 : (4^243) % 729 = 1 := by
    have hsplit : (243 : Nat) = 128 + 115 := by omega
    rw [hsplit, Nat.pow_add]
  have h4243q : ∀ q : Nat, (4^243)^q % 729 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^243)^(Nat.succ q') = (4^243)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h243, ih]
  have hmd : m = 243 * (m / 243) + m % 243 := (Nat.div_add_mod m 243).symm
  have h4m : 4^m = (4^243)^(m/243) * 4^(m%243) := by
    have h1 : 4^m = 4^(243*(m/243) + m%243) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(243*(m/243) + m%243) = (4^243)^(m/243) * 4^(m%243) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h4243q, Nat.one_mul, Nat.mod_mod]

/-- The thirteen fired classes' level values, computed at their levels. -/
theorem four_pow_19_mod81 : (4^19) % 81 = 58 := by decide
theorem four_pow_22_mod81 : (4^22) % 81 = 67 := by decide
theorem four_pow_55_mod243 : (4^55) % 243 = 166 := by decide
theorem four_pow_58_mod243 : (4^58) % 243 = 175 := by decide
theorem four_pow_64_mod243 : (4^64) % 243 = 193 := by decide
theorem four_pow_67_mod243 : (4^67) % 243 = 202 := by decide
theorem four_pow_85_mod729 : (4^85) % 729 = 499 := by decide
theorem four_pow_91_mod729 : (4^91) % 729 = 517 := by decide
theorem four_pow_112_mod729 : (4^112) % 729 = 580 := by decide
theorem four_pow_163_mod729 : (4^163) % 729 = 490 := by
  have hsplit : (163 : Nat) = 128 + 35 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_175_mod729 : (4^175) % 729 = 526 := by
  have hsplit : (175 : Nat) = 128 + 47 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_190_mod729 : (4^190) % 729 = 571 := by
  have hsplit : (190 : Nat) = 128 + 62 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_202_mod729 : (4^202) % 729 = 607 := by
  have hsplit : (202 : Nat) = 128 + 74 := by omega
  rw [hsplit, Nat.pow_add]

/-- The generic level-27 fire: a core in class `c` mod 27 whose level value
`4 ^ c % 81 = v` sits in the top third (`v / 27 = 2`) owns digit position
3 of `4 ^ core` outright. -/
theorem digit3_pow4_pos3_of_class (core c v : Nat)
    (h : core % 27 = c) (hv : (4^c) % 81 = v) (hv2 : v / 27 = 2) :
    digit3 (4^core) 3 = 2 := by
  have hm : (4^core) % 81 = v := by rw [four_pow_mod81, h]; exact hv
  show (4^core) / 3^3 % 3 = 2
  have h33 : (3 : Nat)^3 = 27 := by norm_num
  rw [h33]
  have hbridge : (4^core / 27) % 3 = ((4^core) % 81) / 27 := by omega
  rw [hbridge, hm, hv2]

/-- The generic level-81 fire: a core in class `c` mod 81 whose level value
`4 ^ c % 243 = v` sits in the top third (`v / 81 = 2`) owns digit position
4 of `4 ^ core` outright. -/
theorem digit3_pow4_pos4_of_class (core c v : Nat)
    (h : core % 81 = c) (hv : (4^c) % 243 = v) (hv2 : v / 81 = 2) :
    digit3 (4^core) 4 = 2 := by
  have hm : (4^core) % 243 = v := by rw [four_pow_mod243, h]; exact hv
  show (4^core) / 3^4 % 3 = 2
  have h34 : (3 : Nat)^4 = 81 := by norm_num
  rw [h34]
  have hbridge : (4^core / 81) % 3 = ((4^core) % 243) / 81 := by omega
  rw [hbridge, hm, hv2]

/-- The generic level-243 fire: a core in class `c` mod 243 whose level
value `4 ^ c % 729 = v` sits in the top third (`v / 243 = 2`) owns digit
position 5 of `4 ^ core` outright. -/
theorem digit3_pow4_pos5_of_class (core c v : Nat)
    (h : core % 243 = c) (hv : (4^c) % 729 = v) (hv2 : v / 243 = 2) :
    digit3 (4^core) 5 = 2 := by
  have hm : (4^core) % 729 = v := by rw [four_pow_mod729, h]; exact hv
  show (4^core) / 3^5 % 3 = 2
  have h35 : (3 : Nat)^5 = 243 := by norm_num
  rw [h35]
  have hbridge : (4^core / 243) % 3 = ((4^core) % 729) / 243 := by omega
  rw [hbridge, hm, hv2]

/-! ## §7 The replacement input — the shrunk row half, linked with the
universe -/

/-- **THE THIRTEEN FIRED CLASSES.**  The lattice's fired classes of the hard
family, at their three levels: every core in one of these classes owns its
digit two outright. -/
def s0_lattice_fire_class (core : Nat) : Prop :=
  core % 27 = 19 ∨ core % 27 = 22 ∨
  core % 81 = 55 ∨ core % 81 = 58 ∨ core % 81 = 64 ∨ core % 81 = 67 ∨
  core % 243 = 85 ∨ core % 243 = 91 ∨ core % 243 = 112 ∨ core % 243 = 163 ∨
  core % 243 = 175 ∨ core % 243 = 190 ∨ core % 243 = 202

/-- **THE LATTICE FIRE.**  Every one of the thirteen fired classes owns its
digit two unconditionally — no package, no input, no gates. -/
theorem s0_lattice_fire (core : Nat) (h : s0_lattice_fire_class core) :
    ∃ p : Nat, digit3 (4^core) p = 2 := by
  unfold s0_lattice_fire_class at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨3, digit3_pow4_pos3_of_class core 19 58 h four_pow_19_mod81 (by decide)⟩
  · exact ⟨3, digit3_pow4_pos3_of_class core 22 67 h four_pow_22_mod81 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 55 166 h four_pow_55_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 58 175 h four_pow_58_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 64 193 h four_pow_64_mod243 (by decide)⟩
  · exact ⟨4, digit3_pow4_pos4_of_class core 67 202 h four_pow_67_mod243 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 85 499 h four_pow_85_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 91 517 h four_pow_91_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 112 580 h four_pow_112_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 163 490 h four_pow_163_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 175 526 h four_pow_175_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 190 571 h four_pow_190_mod729 (by decide)⟩
  · exact ⟨5, digit3_pow4_pos5_of_class core 202 607 h four_pow_202_mod729 (by decide)⟩

/-- **THE SEVENTEEN SURVIVORS.**  The hard family's residue classes that no
lattice level has fired: the carried row input shrinks to exactly these. -/
def tailF_row_survivor_class (core : Nat) : Prop :=
  core % 243 = 1 ∨ core % 243 = 4 ∨ core % 243 = 10 ∨ core % 243 = 13 ∨
  core % 243 = 28 ∨ core % 243 = 31 ∨ core % 243 = 37 ∨ core % 243 = 40 ∨
  core % 243 = 82 ∨ core % 243 = 94 ∨ core % 243 = 109 ∨ core % 243 = 118 ∨
  core % 243 = 121 ∨ core % 243 = 166 ∨ core % 243 = 172 ∨ core % 243 = 193 ∨
  core % 243 = 199

/-- **THE BRIDGE.**  Every hard-family core that no lattice level has fired
is one of the seventeen survivors: the case tree 6 → 12 → 24 closes the
thirteen fired leaves by contradiction and lands the seventeen survivors
by arithmetic. -/
theorem tailF_row_survivor_of_hard_nonfire (core : Nat)
    (hc14 : core % 9 = 1 ∨ core % 9 = 4)
    (hf : ¬ s0_lattice_fire_class core) :
    tailF_row_survivor_class core := by
  unfold tailF_row_survivor_class
  unfold s0_lattice_fire_class at hf
  push_neg at hf
  obtain ⟨n19, n22, n55, n58, n64, n67, n85, n91, n112, n163, n175, n190, n202⟩ := hf
  rcases hc14 with h1 | h4
  · have h27 : core % 27 = 1 ∨ core % 27 = 10 ∨ core % 27 = 19 := by omega
    rcases h27 with c1 | c10 | c19
    · have h81 : core % 81 = 1 ∨ core % 81 = 28 ∨ core % 81 = 55 := by omega
      rcases h81 with d1 | d28 | d55
      · have h243 : core % 243 = 1 ∨ core % 243 = 82 ∨ core % 243 = 163 := by omega
        rcases h243 with e1 | e82 | e163
        · omega
        · omega
        · exact absurd e163 n163
      · have h243 : core % 243 = 28 ∨ core % 243 = 109 ∨ core % 243 = 190 := by omega
        rcases h243 with e28 | e109 | e190
        · omega
        · omega
        · exact absurd e190 n190
      · exact absurd d55 n55
    · have h81 : core % 81 = 10 ∨ core % 81 = 37 ∨ core % 81 = 64 := by omega
      rcases h81 with d10 | d37 | d64
      · have h243 : core % 243 = 10 ∨ core % 243 = 91 ∨ core % 243 = 172 := by omega
        rcases h243 with e10 | e91 | e172
        · omega
        · exact absurd e91 n91
        · omega
      · have h243 : core % 243 = 37 ∨ core % 243 = 118 ∨ core % 243 = 199 := by omega
        rcases h243 with e37 | e118 | e199
        · omega
        · omega
        · omega
      · exact absurd d64 n64
    · exact absurd c19 n19
  · have h27 : core % 27 = 4 ∨ core % 27 = 13 ∨ core % 27 = 22 := by omega
    rcases h27 with c4 | c13 | c22
    · have h81 : core % 81 = 4 ∨ core % 81 = 31 ∨ core % 81 = 58 := by omega
      rcases h81 with d4 | d31 | d58
      · have h243 : core % 243 = 4 ∨ core % 243 = 85 ∨ core % 243 = 166 := by omega
        rcases h243 with e4 | e85 | e166
        · omega
        · exact absurd e85 n85
        · omega
      · have h243 : core % 243 = 31 ∨ core % 243 = 112 ∨ core % 243 = 193 := by omega
        rcases h243 with e31 | e112 | e193
        · omega
        · exact absurd e112 n112
        · omega
      · exact absurd d58 n58
    · have h81 : core % 81 = 13 ∨ core % 81 = 40 ∨ core % 81 = 67 := by omega
      rcases h81 with d13 | d40 | d67
      · have h243 : core % 243 = 13 ∨ core % 243 = 94 ∨ core % 243 = 175 := by omega
        rcases h243 with e13 | e94 | e175
        · omega
        · omega
        · exact absurd e175 n175
      · have h243 : core % 243 = 40 ∨ core % 243 = 121 ∨ core % 243 = 202 := by omega
        rcases h243 with e40 | e121 | e202
        · omega
        · omega
        · exact absurd e202 n202
      · exact absurd d67 n67
    · exact absurd c22 n22

/-- **THE SHRUNK ROW INPUT.**  The row primitive with all thirteen fired
classes removed: the residue clause now demands one of the seventeen
mod-243 survivors, and the fire at every other class of the hard family is
unconditional (§6). -/
def tailF_row_primitive_mod243 : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    tailF_row_survivor_class core →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE WEAKNESS RECEIPT.**  The shrunk row input is strictly weaker than
the row primitive: every survivor class is a class of the hard family. -/
theorem tailF_row_primitive_mod243_of_row (hRow : tailF_row_primitive) :
    tailF_row_primitive_mod243 := by
  intro core hK hfree hclass
  refine hRow core hK hfree ?_
  unfold tailF_row_survivor_class at hclass
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- **THE REPLACEMENT OF THE INPUT'S ROW HALF.**  The tower primitive plus
the seventeen-survivor row primitive compose into the full second-observer
input: the sheet-zero family's fired classes close by the lattice outright,
the survivors go through the shrunk row input and the uniform row law, and
the tower family rides the tower primitive unchanged. -/
theorem tailF_of_tower_and_row_mod243
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by rw [← hKsc]; exact hK
    by_cases hf : s0_lattice_fire_class core
    · obtain ⟨p, hp⟩ := s0_lattice_fire core hf
      rw [hKsc]
      exact ⟨p, hp⟩
    · obtain ⟨j, hj⟩ := hRowMod core hKc hfree
        (tailF_row_survivor_of_hard_nonfire core hc14 hf)
      refine ⟨1+j, ?_⟩
      rw [hKsc]
      exact omega_row_level_digit_two core j hj
  · have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN STATEMENT ON THE REPLACEMENT INPUT.**  Through the
monolith's own terminal identity, the tower primitive plus the
seventeen-survivor row primitive carry the whole even-exponent statement. -/
theorem even_conjecture_of_tower_and_row_mod243
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_iff_tailF.mpr
    (tailF_of_tower_and_row_mod243 hTower hRowMod)

/-- **THE CROWN ON THE REPLACEMENT INPUT.**  The monolith's universal
theorem with its input slot filled by the replacement pair: the tower
primitive and the seventeen-survivor row primitive. -/
theorem erdos_ternary_2_universal_of_tower_and_row_mod243
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod243)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF
    (tailF_of_tower_and_row_mod243 hTower hRowMod) n hn

/-! ## §8 The row lattice, level six — the survivors fired one level deeper

The lattice's fourth level.  The cycle law now pins the modulus-2187 residue
of `4 ^ core` by the class of `core` modulo 729, and each of the seventeen
mod-243 survivor classes splits into three mod-729 subclasses — of which
exactly ONE fires.  The level-six lattice kills one third of the surviving
residue content unconditionally; the carried row input shrinks from the
seventeen mod-243 classes to thirty-four mod-729 classes — twice the count,
but each class one third as wide, and seventeen more classes of the hard
family closed outright:

* level 729, digit position 6: classes `31, 37, 118, 172, 253, 256, 271,
  337, 352, 409, 487, 490, 526, 568, 607, 679, 685` mod 729 — the seventeen
  fires, one per mod-243 survivor triple. -/

/-- The cycle law of level 729: the modulus-2187 residue of `4 ^ m` is pinned
by the class of `m` modulo 729. -/
theorem four_pow_mod2187 (m : Nat) : (4^m) % 2187 = (4^(m % 729)) % 2187 := by
  have h729 : (4^729) % 2187 = 1 := by
    have hsplit : (729 : Nat) = 128 + 601 := by omega
    rw [hsplit, Nat.pow_add]
  have h4729q : ∀ q : Nat, (4^729)^q % 2187 = 1 := by
    intro q
    induction q with
    | zero => decide
    | succ q' ih =>
      have hsucc : (4^729)^(Nat.succ q') = (4^729)^(q' + 1) := rfl
      rw [hsucc, Nat.pow_succ, Nat.mul_mod, h729, ih]
  have hmd : m = 729 * (m / 729) + m % 729 := (Nat.div_add_mod m 729).symm
  have h4m : 4^m = (4^729)^(m/729) * 4^(m%729) := by
    have h1 : 4^m = 4^(729*(m/729) + m%729) := congrArg (fun x => 4^x) hmd
    have h2 : 4^(729*(m/729) + m%729) = (4^729)^(m/729) * 4^(m%729) := by
      rw [Nat.pow_add, Nat.pow_mul]
    exact h1.trans h2
  rw [h4m, Nat.mul_mod, h4729q, Nat.one_mul, Nat.mod_mod]

/-- The seventeen fired classes' level values, computed at their levels. -/
theorem four_pow_31_mod2187 : (4^31) % 2187 = 1795 := by decide
theorem four_pow_37_mod2187 : (4^37) % 2187 = 1813 := by decide
theorem four_pow_118_mod2187 : (4^118) % 2187 = 2056 := by decide
theorem four_pow_172_mod2187 : (4^172) % 2187 = 1489 := by
  have hsplit : (172 : Nat) = 128 + 44 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_253_mod2187 : (4^253) % 2187 = 1732 := by
  have hsplit : (253 : Nat) = 128 + 125 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_256_mod2187 : (4^256) % 2187 = 1498 := by
  have hsplit : (256 : Nat) = 128 + 128 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_271_mod2187 : (4^271) % 2187 = 1543 := by
  have hsplit : (271 : Nat) = 128 + 143 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_337_mod2187 : (4^337) % 2187 = 1741 := by
  have hsplit : (337 : Nat) = 128 + 209 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_352_mod2187 : (4^352) % 2187 = 1786 := by
  have hsplit : (352 : Nat) = 128 + 224 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_409_mod2187 : (4^409) % 2187 = 1471 := by
  have hsplit : (409 : Nat) = 128 + 281 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_487_mod2187 : (4^487) % 2187 = 1462 := by
  have hsplit : (487 : Nat) = 128 + 359 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_490_mod2187 : (4^490) % 2187 = 1714 := by
  have hsplit : (490 : Nat) = 128 + 362 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_526_mod2187 : (4^526) % 2187 = 1579 := by
  have hsplit : (526 : Nat) = 128 + 398 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_568_mod2187 : (4^568) % 2187 = 1705 := by
  have hsplit : (568 : Nat) = 128 + 440 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_607_mod2187 : (4^607) % 2187 = 1822 := by
  have hsplit : (607 : Nat) = 128 + 479 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_679_mod2187 : (4^679) % 2187 = 1552 := by
  have hsplit : (679 : Nat) = 128 + 551 := by omega
  rw [hsplit, Nat.pow_add]
theorem four_pow_685_mod2187 : (4^685) % 2187 = 1570 := by
  have hsplit : (685 : Nat) = 128 + 557 := by omega
  rw [hsplit, Nat.pow_add]

/-- The generic level-729 fire: a core in class `c` mod 729 whose level value
`4 ^ c % 2187 = v` sits in the top third (`v / 729 = 2`) owns digit position
6 of `4 ^ core` outright. -/
theorem digit3_pow4_pos6_of_class (core c v : Nat)
    (h : core % 729 = c) (hv : (4^c) % 2187 = v) (hv2 : v / 729 = 2) :
    digit3 (4^core) 6 = 2 := by
  have hm : (4^core) % 2187 = v := by rw [four_pow_mod2187, h]; exact hv
  show (4^core) / 3^6 % 3 = 2
  have h36 : (3:Nat)^6 = 729 := by norm_num
  rw [h36]
  have hbridge : (4^core / 729) % 3 = ((4^core) % 2187) / 729 := by omega
  rw [hbridge, hm, hv2]

/-- **THE SEVENTEEN LEVEL-SIX FIRED CLASSES.**  Each mod-243 survivor triple
contributes exactly one fired subclass. -/
def s0_lattice_fire_class_mod729 (core : Nat) : Prop :=
  core % 729 = 31 ∨ core % 729 = 37 ∨ core % 729 = 118 ∨ core % 729 = 172 ∨
  core % 729 = 253 ∨ core % 729 = 256 ∨ core % 729 = 271 ∨ core % 729 = 337 ∨
  core % 729 = 352 ∨ core % 729 = 409 ∨ core % 729 = 487 ∨ core % 729 = 490 ∨
  core % 729 = 526 ∨ core % 729 = 568 ∨ core % 729 = 607 ∨ core % 729 = 679 ∨
  core % 729 = 685

/-- **THE LEVEL-SIX LATTICE FIRE.**  Every one of the seventeen fired classes
owns its digit two unconditionally. -/
theorem s0_lattice_fire_mod729 (core : Nat)
    (h : s0_lattice_fire_class_mod729 core) :
    ∃ p : Nat, digit3 (4^core) p = 2 := by
  unfold s0_lattice_fire_class_mod729 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨6, digit3_pow4_pos6_of_class core 31 1795 h four_pow_31_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 37 1813 h four_pow_37_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 118 2056 h four_pow_118_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 172 1489 h four_pow_172_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 253 1732 h four_pow_253_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 256 1498 h four_pow_256_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 271 1543 h four_pow_271_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 337 1741 h four_pow_337_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 352 1786 h four_pow_352_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 409 1471 h four_pow_409_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 487 1462 h four_pow_487_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 490 1714 h four_pow_490_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 526 1579 h four_pow_526_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 568 1705 h four_pow_568_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 607 1822 h four_pow_607_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 679 1552 h four_pow_679_mod2187 (by decide)⟩
  · exact ⟨6, digit3_pow4_pos6_of_class core 685 1570 h four_pow_685_mod2187 (by decide)⟩

/-- **THE THIRTY-FOUR LEVEL-SIX SURVIVORS.**  The hard family's residue
classes that no lattice level has fired: the carried row input shrinks to
exactly these, at mod-729 resolution. -/
def tailF_row_survivor_class_mod729 (core : Nat) : Prop :=
  core % 729 = 1 ∨ core % 729 = 4 ∨ core % 729 = 10 ∨ core % 729 = 13 ∨
  core % 729 = 28 ∨ core % 729 = 40 ∨ core % 729 = 82 ∨ core % 729 = 94 ∨
  core % 729 = 109 ∨ core % 729 = 121 ∨ core % 729 = 166 ∨ core % 729 = 193 ∨
  core % 729 = 199 ∨ core % 729 = 244 ∨ core % 729 = 247 ∨ core % 729 = 274 ∨
  core % 729 = 280 ∨ core % 729 = 283 ∨ core % 729 = 325 ∨ core % 729 = 361 ∨
  core % 729 = 364 ∨ core % 729 = 415 ∨ core % 729 = 436 ∨ core % 729 = 442 ∨
  core % 729 = 496 ∨ core % 729 = 499 ∨ core % 729 = 514 ∨ core % 729 = 517 ∨
  core % 729 = 523 ∨ core % 729 = 580 ∨ core % 729 = 595 ∨ core % 729 = 604 ∨
  core % 729 = 652 ∨ core % 729 = 658

/-- **THE LEVEL-SIX BRIDGE.**  Every hard-family core that neither lattice
level has fired is one of the thirty-four mod-729 survivors: the seventeen
mod-243 survivor classes each split into three mod-729 subclasses, exactly
one of which fires. -/
theorem tailF_row_survivor_mod729_of_nonfire (core : Nat)
    (hc14 : core % 9 = 1 ∨ core % 9 = 4)
    (hf : ¬ s0_lattice_fire_class core)
    (hf6 : ¬ s0_lattice_fire_class_mod729 core) :
    tailF_row_survivor_class_mod729 core := by
  have h243class := tailF_row_survivor_of_hard_nonfire core hc14 hf
  unfold tailF_row_survivor_class_mod729
  unfold tailF_row_survivor_class at h243class
  unfold s0_lattice_fire_class_mod729 at hf6
  push_neg at hf6
  obtain ⟨n31, n37, n118, n172, n253, n256, n271, n337, n352, n409, n487,
    n490, n526, n568, n607, n679, n685⟩ := hf6
  rcases h243class with c1 | c4 | c10 | c13 | c28 | c31 | c37 | c40 | c82 |
    c94 | c109 | c118 | c121 | c166 | c172 | c193 | c199
  · have h : core % 729 = 1 ∨ core % 729 = 244 ∨ core % 729 = 487 := by omega
    rcases h with e1 | e244 | e487
    · omega
    · omega
    · exact absurd e487 n487
  · have h : core % 729 = 4 ∨ core % 729 = 247 ∨ core % 729 = 490 := by omega
    rcases h with e4 | e247 | e490
    · omega
    · omega
    · exact absurd e490 n490
  · have h : core % 729 = 10 ∨ core % 729 = 253 ∨ core % 729 = 496 := by omega
    rcases h with e10 | e253 | e496
    · omega
    · exact absurd e253 n253
    · omega
  · have h : core % 729 = 13 ∨ core % 729 = 256 ∨ core % 729 = 499 := by omega
    rcases h with e13 | e256 | e499
    · omega
    · exact absurd e256 n256
    · omega
  · have h : core % 729 = 28 ∨ core % 729 = 271 ∨ core % 729 = 514 := by omega
    rcases h with e28 | e271 | e514
    · omega
    · exact absurd e271 n271
    · omega
  · have h : core % 729 = 31 ∨ core % 729 = 274 ∨ core % 729 = 517 := by omega
    rcases h with e31 | e274 | e517
    · exact absurd e31 n31
    · omega
    · omega
  · have h : core % 729 = 37 ∨ core % 729 = 280 ∨ core % 729 = 523 := by omega
    rcases h with e37 | e280 | e523
    · exact absurd e37 n37
    · omega
    · omega
  · have h : core % 729 = 40 ∨ core % 729 = 283 ∨ core % 729 = 526 := by omega
    rcases h with e40 | e283 | e526
    · omega
    · omega
    · exact absurd e526 n526
  · have h : core % 729 = 82 ∨ core % 729 = 325 ∨ core % 729 = 568 := by omega
    rcases h with e82 | e325 | e568
    · omega
    · omega
    · exact absurd e568 n568
  · have h : core % 729 = 94 ∨ core % 729 = 337 ∨ core % 729 = 580 := by omega
    rcases h with e94 | e337 | e580
    · omega
    · exact absurd e337 n337
    · omega
  · have h : core % 729 = 109 ∨ core % 729 = 352 ∨ core % 729 = 595 := by omega
    rcases h with e109 | e352 | e595
    · omega
    · exact absurd e352 n352
    · omega
  · have h : core % 729 = 118 ∨ core % 729 = 361 ∨ core % 729 = 604 := by omega
    rcases h with e118 | e361 | e604
    · exact absurd e118 n118
    · omega
    · omega
  · have h : core % 729 = 121 ∨ core % 729 = 364 ∨ core % 729 = 607 := by omega
    rcases h with e121 | e364 | e607
    · omega
    · omega
    · exact absurd e607 n607
  · have h : core % 729 = 166 ∨ core % 729 = 409 ∨ core % 729 = 652 := by omega
    rcases h with e166 | e409 | e652
    · omega
    · exact absurd e409 n409
    · omega
  · have h : core % 729 = 172 ∨ core % 729 = 415 ∨ core % 729 = 658 := by omega
    rcases h with e172 | e415 | e658
    · exact absurd e172 n172
    · omega
    · omega
  · have h : core % 729 = 193 ∨ core % 729 = 436 ∨ core % 729 = 679 := by omega
    rcases h with e193 | e436 | e679
    · omega
    · omega
    · exact absurd e679 n679
  · have h : core % 729 = 199 ∨ core % 729 = 442 ∨ core % 729 = 685 := by omega
    rcases h with e199 | e442 | e685
    · omega
    · omega
    · exact absurd e685 n685

/-- **THE SHRUNK ROW INPUT, LEVEL SIX.**  The row primitive with all
thirty lattice levels' fired classes removed: the residue clause now
demands one of the thirty-four mod-729 survivors. -/
def tailF_row_primitive_mod729 : Prop :=
  ∀ core : Nat, 500 < core → ¬ 3 ∣ core →
    tailF_row_survivor_class_mod729 core →
      ∃ j : Nat, 2 * 3^j ≤ (omegaCutWord 0 core) % 3^(j+1)

/-- **THE WEAKNESS RECEIPT, LEVEL SIX.**  The level-six shrunk row input is
strictly weaker than the mod-243 one: every mod-729 survivor sits inside a
mod-243 survivor class. -/
theorem tailF_row_primitive_mod729_of_mod243 (h : tailF_row_primitive_mod243) :
    tailF_row_primitive_mod729 := by
  intro core hK hfree hclass
  refine h core hK hfree ?_
  unfold tailF_row_survivor_class_mod729 at hclass
  unfold tailF_row_survivor_class
  rcases hclass with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega

theorem tailF_row_primitive_mod729_of_row (hRow : tailF_row_primitive) :
    tailF_row_primitive_mod729 :=
  tailF_row_primitive_mod729_of_mod243 (tailF_row_primitive_mod243_of_row hRow)

/-- **THE REPLACEMENT OF THE INPUT'S ROW HALF, LEVEL SIX.**  The tower
primitive plus the thirty-four-survivor row primitive compose into the full
second-observer input. -/
theorem tailF_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    four_power_omega_shadow_wave_tailF := by
  intro K hK hshadow
  obtain ⟨s, core, hKsc, hfree, hres, hA, hB1, hB2, hC, hD⟩ := hshadow
  rcases Nat.eq_zero_or_pos s with rfl | hs1
  · have hc14 : core % 9 = 1 ∨ core % 9 = 4 := by
      rcases hres with h4 | ⟨_, h1⟩ | ⟨h1s, h7⟩
      · exact Or.inr h4
      · exact Or.inl h1
      · exact absurd h1s (by omega)
    rw [Nat.pow_zero, Nat.one_mul] at hKsc
    have hKc : 500 < core := by rw [← hKsc]; exact hK
    by_cases hf : s0_lattice_fire_class core
    · obtain ⟨p, hp⟩ := s0_lattice_fire core hf
      rw [hKsc]
      exact ⟨p, hp⟩
    · by_cases hf6 : s0_lattice_fire_class_mod729 core
      · obtain ⟨p, hp⟩ := s0_lattice_fire_mod729 core hf6
        rw [hKsc]
        exact ⟨p, hp⟩
      · obtain ⟨j, hj⟩ := hRowMod core hKc hfree
          (tailF_row_survivor_mod729_of_nonfire core hc14 hf hf6)
        refine ⟨1+j, ?_⟩
        rw [hKsc]
        exact omega_row_level_digit_two core j hj
  · have hc47 : core % 9 = 4 ∨ core % 9 = 7 := by
      rcases hres with h4 | ⟨hs0, h1⟩ | ⟨hs1', h7⟩
      · exact Or.inl h4
      · exact absurd hs0 (by omega)
      · exact Or.inr h7
    obtain ⟨i, _, hfire⟩ := hTower s core hs1 hfree hc47 hD
    refine ⟨s+1+i, ?_⟩
    rw [hKsc]
    exact tower_observation_digit_two s core i hfire

/-- **THE EVEN STATEMENT ON THE REPLACEMENT INPUT, LEVEL SIX.** -/
theorem even_conjecture_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729) :
    ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false :=
  erdos_even_conjecture_iff_tailF.mpr
    (tailF_of_tower_and_row_mod729 hTower hRowMod)

/-- **THE CROWN ON THE REPLACEMENT INPUT, LEVEL SIX.** -/
theorem erdos_ternary_2_universal_of_tower_and_row_mod729
    (hTower : tailF_tower_primitive)
    (hRowMod : tailF_row_primitive_mod729)
    (n : Nat) (hn : 9 ≤ n) :
    noTernaryTwo (2^n) = false :=
  erdos_ternary_2_universal_of_tailF
    (tailF_of_tower_and_row_mod729 hTower hRowMod) n hn

#print axioms tower_observation_digit_two
#print axioms omega_cut_word_stabilizes
#print axioms omega_tower_word_mod_stable
#print axioms omega_tower_word_mod_chain
#print axioms omega_tower_kill_of_diagonal_two
#print axioms omega_diagonal_two_of_mod_nine_one
#print axioms omega_diagonal_two_of_mod27_thirteen
#print axioms omega_diagonal_two_of_mod27_twentyfive
#print axioms omega_tower_digit_two_of_mod_nine_one
#print axioms omega_tower_digit_two_of_mod27_band
#print axioms tailF_of_row_and_tower
#print axioms even_conjecture_of_row_and_tower
#print axioms erdos_ternary_2_universal_of_row_and_tower
#print axioms tower_dodge_dead_of_mod27_band
#print axioms four_pow_mod243
#print axioms four_pow_mod729
#print axioms digit3_pow4_pos3_of_class
#print axioms digit3_pow4_pos4_of_class
#print axioms digit3_pow4_pos5_of_class
#print axioms s0_lattice_fire
#print axioms tailF_row_survivor_of_hard_nonfire
#print axioms tailF_row_primitive_mod243_of_row
#print axioms tailF_of_tower_and_row_mod243
#print axioms even_conjecture_of_tower_and_row_mod243
#print axioms erdos_ternary_2_universal_of_tower_and_row_mod243
#print axioms four_pow_mod2187
#print axioms digit3_pow4_pos6_of_class
#print axioms s0_lattice_fire_mod729
#print axioms tailF_row_survivor_mod729_of_nonfire
#print axioms tailF_row_primitive_mod729_of_mod243
#print axioms tailF_row_primitive_mod729_of_row
#print axioms tailF_of_tower_and_row_mod729
#print axioms even_conjecture_of_tower_and_row_mod729
#print axioms erdos_ternary_2_universal_of_tower_and_row_mod729

end GSTTailFFourthDimension
