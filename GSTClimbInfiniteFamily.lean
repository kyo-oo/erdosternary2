import Mathlib
import GSTTheAct
import GSTDiagonalRead
import GSTFourPowerHappyProvider
import GSTCanonicalTailLTE
import GSTCanonicalTailStateIso
import GSTFourPowerDirectAdditionCarry

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

/-!
# THE COMPLETED READ, FILLED INTO THE CLIMB FAMILY

One separate file, zero monolith bytes.  The diagonal window law,
completed to the whole plane and filled in:

* **§0 THE ACT AND THE ANSWER (base, below).**  `the_act`, its identity
  with `hTailF`'s target, and the one-line answer live in `GSTTheAct` —
  the base module this file is built on.  This file is the container
  where the completion lands.

* **§1 THE INFINITE CLIMB FAMILY.**  The climb itself is GREEN on an
  infinite, unbounded family of exponents: every `K = 3^v · u` with `v ≥ 2`
  and `u ≡ 2 mod 3` owns its Happy row at `v+1`.

* **§2 THE PREFACED READ — the completion of the diagonal window law.**
  `prefaced_window_law`: for EVERY cut `v`, EVERY core `u`, EVERY
  remainder `r < 3^v` — no coprimality, no zero-remainder restriction —
  the digit stream of `4^(3^v·u + r)` at rows `v+1 .. 2v+1` is the digit
  stream of the explicit prefaced object `4^r + 3^(v+1)·(4^r·c(v)·u)`.
  `prefaced_window_full` slices it cleanly at EVERY remainder: those rows
  ARE the trits of `4^r/3^(v+1) + 4^r·c(v)·u`.  `every_row_is_read`: at
  the cut `v = p-1` the law covers row `p` — EVERY row of EVERY power of
  four, the whole plane, one law.  The free zone is open.

* **§3 THE CASCADE — the v=0 dust ladder.**  The dust's largest layer —
  every exponent `K ≡ 1 mod 3` — is eaten level by level by the prefaced
  read at the first cuts: `K ≡ 7 mod 9` fires at row 2;
  `K ≡ 19, 22, 25 mod 27` fire at row 3; `K ≡ 55, 58, 64, 67, 73, 76
  mod 81` fire at row 4 — all infinite uniform families, all through the
  repo's own kill chain (`no22_of_cascade`).

* **§4 THE COLLAPSE — the core, exactly.**  `CantorianPower`: an
  exponent whose power of four carries NO digit two at any row from one
  upward.  `the_act_iff_no_cantorian`: the act holds IF AND ONLY IF no
  exponent from eight on is Cantorian — the read's residual collapses
  from the window-clean dust to exactly the Erdős core, nothing else.
  `hTailF_of_no_cantorian`: the final socket — no Cantorian exponent
  from eight on ⇒ `hTailF`, no hypothesis, no binder beyond the core.
  `cantorian_survivors_below_eight`: the core's only members below the
  floor are `0, 1, 4` — the powers `1, 4, 256` — machine-named.

* **§5 THE RECEIPT.**  Everything assembled in one theorem, with axiom
  printouts: the classical three only.
-/

namespace GSTClimbInfiniteFamily

open GSTCanonicalSevenAxisBridge (digit3 carry4)
open GSTU2DEventTransport (HappyCell)

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
      digit3 (4^(K % 3^(p-1)) + 3^(p-1+1) *
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
  rw [show A * u = u + 3 * (3 * k * u) from by rw [hk]; ring]
  omega

/-- Row one of `q + A·u` reads the core's own row one when the preface
quotient vanishes mod nine and the coefficient is `1 mod 9`: the preface
drops out of the second trit. -/
theorem digit3_one_of_preface (q A u : Nat) (hq : q % 9 = 0) (hA : A % 9 = 1) :
    digit3 (q + A * u) 1 = (u / 3) % 3 := by
  obtain ⟨k, hk⟩ : ∃ k : Nat, A = 1 + 9 * k := ⟨A / 9, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : Nat, q = 9 * m := ⟨q / 9, by omega⟩
  unfold digit3
  rw [show q + A * u = u + 3 * (3 * k * u + 3 * m) from by rw [hk, hm]; ring]
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
    · push_neg at hCant
      obtain ⟨p, _, hp⟩ := hCant
      exact has_two_imp_not_no_two (4^K)
        (hasTernaryTwo_of_digit (4^K) p (by simpa [digit3] using hp))

/-- **THE FINAL SOCKET.**  No Cantorian exponent from eight on ⇒ the act
⇒ `hTailF`: the whole conditionality of `hTailF` collapses onto the
Cantorian core alone — no hypothesis, no binder beyond the core itself. -/
theorem hTailF_of_no_cantorian
    (h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K) :
    GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF :=
  GSTTheAct.the_act_iff_hTailF.mp (the_act_iff_no_cantorian.mp h)

/-- `K = 0` is Cantorian: `4^0 = 1` has no trits at all above row zero. -/
theorem cantorian_zero : CantorianPower 0 := by
  intro p hp
  unfold digit3
  rw [Nat.pow_zero]
  have h1 : 1 < 3^p := by
    have h3 : 3^1 ≤ 3^p := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
    norm_num at h3
    omega
  rw [Nat.div_eq_of_lt h1]
  decide

/-- `K = 1` is Cantorian: `4 = 11₃`. -/
theorem cantorian_one : CantorianPower 1 := by
  intro p hp
  have h4 : (4:Nat)^1 = 4 := by norm_num
  unfold digit3
  rw [h4]
  rcases Nat.lt_or_ge p 2 with h2 | h2
  · have hp1 : p = 1 := by omega
    subst hp1
    decide
  · have h9 : 4 < 3^p := by
      have h3 : 3^2 ≤ 3^p := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      norm_num at h3
      omega
    rw [Nat.div_eq_of_lt h9]
    decide

/-- `K = 4` is Cantorian: `256 = 100111₃`. -/
theorem cantorian_four : CantorianPower 4 := by
  intro p hp
  have h256 : (4:Nat)^4 = 256 := by norm_num
  unfold digit3
  rw [h256]
  rcases Nat.lt_or_ge p 6 with h6 | h6
  · interval_cases p
    · decide
    · decide
    · decide
    · decide
    · decide
  · have h729 : 256 < 3^p := by
      have h3 : 3^6 ≤ 3^p := Nat.pow_le_pow_of_le (by decide : 1 < 3) (by omega)
      norm_num at h3
      omega
    rw [Nat.div_eq_of_lt h729]
    decide

/-- `K = 2` is not Cantorian: `16 = 121₃` fires at row one. -/
theorem not_cantorian_two : ¬ CantorianPower 2 := by
  intro h
  exact h 1 (by omega) (by decide)

/-- `K = 3` is not Cantorian: `64 = 2101₃` fires at row three. -/
theorem not_cantorian_three : ¬ CantorianPower 3 := by
  intro h
  exact h 3 (by omega) (by decide)

/-- `K = 5` is not Cantorian: `1024 = 1101221₃` fires at row two. -/
theorem not_cantorian_five : ¬ CantorianPower 5 := by
  intro h
  exact h 2 (by omega) (by decide)

/-- `K = 6` is not Cantorian: `4096 = 12121201₃` fires at row two. -/
theorem not_cantorian_six : ¬ CantorianPower 6 := by
  intro h
  exact h 2 (by omega) (by decide)

/-- `K = 7` is not Cantorian: `16384 = 211110211₃` fires at row eight. -/
theorem not_cantorian_seven : ¬ CantorianPower 7 := by
  intro h
  exact h 8 (by omega) (by decide)

/-- **THE CORE BELOW THE FLOOR.**  The Cantorian powers below eight are
exactly the three Erdős survivors `0, 1, 4` — the powers `1, 4, 256` —
machine-named, nothing else. -/
theorem cantorian_survivors_below_eight :
    CantorianPower 0 ∧ CantorianPower 1 ∧ CantorianPower 4 ∧
      ¬ CantorianPower 2 ∧ ¬ CantorianPower 3 ∧ ¬ CantorianPower 5 ∧
      ¬ CantorianPower 6 ∧ ¬ CantorianPower 7 :=
  ⟨cantorian_zero, cantorian_one, cantorian_four,
    not_cantorian_two, not_cantorian_three, not_cantorian_five,
    not_cantorian_six, not_cantorian_seven⟩

/-! ## §5 THE RECEIPT — everything in one theorem -/

/-- **THE COMPLETED READ, ASSEMBLED.**  (1) The prefaced window law,
sliced at every remainder.  (2) Every row of every power is read.  (3)
The cascade's three levels.  (4) The collapse: the act ⟺ no Cantorian
exponent from eight on.  (5) The final socket.  (6) The core's
below-floor survivors.  (7) The cascade kill.  (8) The climb family.  (9)
The family is unbounded. -/
theorem the_completed_read_receipt :
    (∀ v u r j : Nat, r < 3^v → j ≤ v →
      digit3 (4^(3^v * u + r)) (v + 1 + j) =
        digit3 (4^r / 3^(v+1) + 4^r * GSTCanonicalTailLTE.lteCoeff v * u) j) ∧
    (∀ K p : Nat, 1 ≤ p →
      digit3 (4^K) p =
        digit3 (4^(K % 3^(p-1)) + 3^(p-1+1) *
          (4^(K % 3^(p-1)) * GSTCanonicalTailLTE.lteCoeff (p-1) *
            (K / 3^(p-1)))) p) ∧
    (∀ K : Nat, K % 9 = 7 → digit3 (4^K) 2 = 2) ∧
    (∀ K : Nat, K % 27 = 19 ∨ K % 27 = 22 ∨ K % 27 = 25 →
      digit3 (4^K) 3 = 2) ∧
    (∀ K : Nat, K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨ K % 81 = 67 ∨
        K % 81 = 73 ∨ K % 81 = 76 →
      digit3 (4^K) 4 = 2) ∧
    (GSTTheAct.the_act ↔ ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K) ∧
    (∀ h : ¬ ∃ K : Nat, 8 ≤ K ∧ CantorianPower K,
        GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF) ∧
    (CantorianPower 0 ∧ CantorianPower 1 ∧ CantorianPower 4 ∧
      ¬ CantorianPower 2 ∧ ¬ CantorianPower 3 ∧ ¬ CantorianPower 5 ∧
      ¬ CantorianPower 6 ∧ ¬ CantorianPower 7) ∧
    (∀ K : Nat, K % 9 = 7 ∨ K % 27 = 19 ∨ K % 27 = 22 ∨ K % 27 = 25 ∨
        K % 81 = 55 ∨ K % 81 = 58 ∨ K % 81 = 64 ∨ K % 81 = 67 ∨
        K % 81 = 73 ∨ K % 81 = 76 →
      noTernaryTwo (4^K) = false) ∧
    (∀ K : Nat, wave3_deep_member K →
      ∃ p : Nat, 3 ≤ p ∧ HappyCell (carry4 (4^K) p) (digit3 (4^K) p)) ∧
    (∀ N : Nat, ∃ K : Nat, N ≤ K ∧ wave3_deep_member K) :=
  ⟨prefaced_window_full, every_row_is_read, dust_fire_row_two,
    dust_fire_row_three, dust_fire_row_four, the_act_iff_no_cantorian,
    hTailF_of_no_cantorian, cantorian_survivors_below_eight,
    no22_of_cascade, climb_member_of_wave3_deep, wave3_deep_unbounded⟩

#print axioms pair_law
#print axioms climb_member_of_wave3_deep
#print axioms member_eighteen
#print axioms climb_witness_eighteen
#print axioms pow_ge_self
#print axioms wave3_deep_unbounded
#print axioms prefaced_window_law
#print axioms prefaced_window_full
#print axioms prefaced_window_sliced
#print axioms every_row_is_read
#print axioms digit3_one_of_mod9
#print axioms digit3_one_of_preface
#print axioms dust_row_two
#print axioms dust_row_three
#print axioms dust_row_four_one
#print axioms dust_row_four_four
#print axioms dust_fire_row_two
#print axioms dust_fire_row_three
#print axioms dust_fire_row_four
#print axioms no22_of_digit_two
#print axioms no22_of_cascade
#print axioms pow4_mod3
#print axioms noTernaryTwo_of_forall_digit
#print axioms cantorian_no_two
#print axioms the_act_iff_no_cantorian
#print axioms hTailF_of_no_cantorian
#print axioms cantorian_zero
#print axioms cantorian_one
#print axioms cantorian_four
#print axioms not_cantorian_two
#print axioms not_cantorian_three
#print axioms not_cantorian_five
#print axioms not_cantorian_six
#print axioms not_cantorian_seven
#print axioms cantorian_survivors_below_eight
#print axioms the_completed_read_receipt

end GSTClimbInfiniteFamily
