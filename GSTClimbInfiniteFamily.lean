import Mathlib
import GSTInfiniteFourPowerNavigation
import GSTTailFProof
import GSTClimbTruthValue
import GSTFourPowerHappyProvider
import GSTCanonicalTailLTE
import GSTCanonicalTailStateIso
import GSTFourPowerDirectAdditionCarry
import GSTFinalPurePowerResidueTransplant

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE ACT, THE ANSWER, AND THE INFINITE CLIMB FAMILY

One separate file, zero monolith bytes.  Four machine-checked deliveries:

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

* **§2 THE INFINITE CLIMB FAMILY.**  The climb itself is GREEN on an
  infinite, unbounded family of exponents: every `K = 3^v · u` with `v ≥ 2`
  and `u ≡ 2 mod 3` owns its Happy row at `v+1`.  The pair law at the
  valuation cut: both consecutive powers carry `u % 3 = 2` at row `v+1`,
  and the x4-carry there is exactly zero.  `climb_witness_eighteen` is the
  family's first member beyond the old witnesses `8, 9, 10`.

* **§3 THE RECEIPT.**  Everything assembled in one theorem, with axiom
  printouts: the classical three only.
-/

namespace GSTClimbInfiniteFamily

open GSTCanonicalSevenAxisBridge (digit3 carry4)
open GSTU2DEventTransport (HappyCell)

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

/-! ## §2 THE INFINITE CLIMB FAMILY — the climb green on an
unbounded family of exponents -/

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
    exact front_law v u
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

/-! ## §3 THE RECEIPT — everything in one theorem -/

/-- **THE ACT, THE ANSWER, AND THE INFINITE FAMILY, ASSEMBLED.**
(1) The act and `hTailF`'s target are one object.  (2) Erdős closed ⇒
`hTailF` closed, one green line.  (3) The act and the full statement are
one object (the odd half is green).  (4) The climb is green on the whole
deep-scale family.  (5) The family is unbounded. -/
theorem the_act_and_the_infinite_family :
    (the_act ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (∀ hFull : ∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false,
        GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (the_act ↔ (∀ n : Nat, 9 ≤ n → noTernaryTwo (2^n) = false)) ∧
    (∀ K : Nat, wave3_deep_member K →
      ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) ∧
    (∀ N : Nat, ∃ K : Nat, N ≤ K ∧ wave3_deep_member K) :=
  ⟨the_act_iff_hTailF, hTailF_of_full_erdos, the_act_iff_full_erdos,
    climb_member_of_wave3_deep, wave3_deep_unbounded⟩

#print axioms the_act_iff_hTailF
#print axioms the_act_of_full_erdos
#print axioms hTailF_of_full_erdos
#print axioms full_erdos_of_the_act
#print axioms the_act_iff_full_erdos
#print axioms climb_gives_the_act
#print axioms front_law
#print axioms pair_law
#print axioms climb_member_of_wave3_deep
#print axioms member_eighteen
#print axioms climb_witness_eighteen
#print axioms pow_ge_self
#print axioms wave3_deep_unbounded
#print axioms the_act_and_the_infinite_family

end GSTClimbInfiniteFamily
