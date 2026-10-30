import GSTProblem406GSTPeelFixedPoint
import GSTFourPowerThirdWave

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

/-!
GST-native all-ones exponent physical collision at row m+9.
This uses the exact peel1 polynomial and a fixed source coefficient 14049
rather than a generic infinite controller or an assumed hGate.

The target is CommonTwo(ternaryOnes m), ALL m>=8. Its proof relies
on one finite base instance and an all-m polynomial stability induction.
-/

namespace GSTProblem406AllOnesFirstCollision

open GSTFourPowerDirectResidue
open GSTFourPowerDirectExistence
open GSTFourPowerAffineOrbit
open GSTFourPowerAffineExponentPeel
open GSTProblem406GSTPeelFixedPoint

/-- The source-specific stabilized nine-trit affine fixed core. -/
private def stableCore (m : Nat) : Nat :=
  ternaryOnes m + 3^m * 14049

private theorem stableCore_succ (m : Nat) :
    stableCore (m+1) = 1 + 3*stableCore m := by
  simp only [stableCore, ternaryOnes, pow_succ]
  ring

/-- True finite-core GST nonlinear fixed point, all m>=8. -/
private theorem stableCore_peel1_fixed
    (m : Nat) (hm : 8 ≤ m) :
    peel1 (stableCore m) % 3^(m+9) =
      stableCore m % 3^(m+9) := by
  have hshift : 2*stableCore m+1 = 3^m*28099 := by
    unfold stableCore
    have h := ternaryOnes_identity m
    omega
  have hdiv : 3^(m+9) ∣
      3*stableCore m*(2*stableCore m+1)^2 := by
    have hpower : 3^(m+9) ∣ 3^(2*m+1) :=
      Nat.pow_dvd_pow 3 (by omega)
    have hbig : 3^(2*m+1) ∣
        3*stableCore m*(2*stableCore m+1)^2 := by
      refine ⟨stableCore m * 28099^2, ?_⟩
      rw [hshift]
      have hp : 3^(2*m+1) = 3*(3^m)^2 := by
        rw [show 2*m+1=m*2+1 by omega, pow_succ, pow_mul]
        ring
      rw [hp]
      ring
    exact dvd_trans hpower hbig
  rw [peel1_exact_nonarchimedean_fixedpoint, Nat.add_mod,
      Nat.mod_eq_zero_of_dvd hdiv]
  simp

/-- The exact physical affineOrbit has this stabilized 9-trit prefix
for every ALL-ONES exponent length m>=8. This is an all-m induction. -/
private theorem physical_affine_stableCore_mod
    (m : Nat) (hm : 8 ≤ m) :
    affineOrbit (ternaryOnes m) % 3^(m+9) =
      stableCore m % 3^(m+9) := by
  obtain ⟨t, rfl⟩ : ∃ t : Nat, m = 8+t :=
    ⟨m-8, by omega⟩
  induction t with
  | zero =>
      decide
  | succ t ih =>
      have hpoly :
          peel1 (affineOrbit (ternaryOnes (8+t))) %
              3^((8+t)+9) =
          peel1 (stableCore (8+t)) % 3^((8+t)+9) := by
        simp [peel1, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, ih]
      have hfix := stableCore_peel1_fixed (8+t) (by omega)
      have htotal : peel1 (affineOrbit (ternaryOnes (8+t))) ≡
          stableCore (8+t) [MOD 3^((8+t)+9)] :=
        hpoly.trans hfix
      have hadd := (htotal.mul_left' 3).add_left 1
      have hstep :
          (1+3*peel1 (affineOrbit (ternaryOnes (8+t)))) %
              3^((8+t)+10) =
          (1+3*stableCore (8+t)) % 3^((8+t)+10) := by
        have hp : 3^((8+t)+10) = 3*3^((8+t)+9) := by
          rw [show (8+t)+10=((8+t)+9)+1 by omega, pow_succ]
          ring
        rw [hp]
        change
          (1+3*peel1 (affineOrbit (ternaryOnes (8+t)))) %
              (3*3^((8+t)+9)) =
          (1+3*stableCore (8+t)) % (3*3^((8+t)+9))
          at hadd
        exact hadd
      change
        affineOrbit (ternaryOnes ((8+t)+1)) % 3^((8+t)+10) =
          stableCore ((8+t)+1) % 3^((8+t)+10)
      rw [ternaryOnes, affineOrbit_three_mul_add_one, stableCore_succ]
      exact hstep

/-- The literal stabilized source has digit 2 at affine row m+8. -/
private theorem source_stableCore_hit (m : Nat) :
    digit3 (stableCore m) (m+8) = 2 := by
  unfold digit3 stableCore
  have hp : 3^(m+8) = 3^m*3^8 := by rw [pow_add]
  rw [hp, ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt (ternaryOnes_lt_pow m)]
  norm_num

/-- The ORIGINAL neighboring affine source also has digit 2
at that SAME affine row m+8. -/
private theorem neighbor_stableCore_hit (m : Nat) :
    digit3 (4*stableCore m+1) (m+8) = 2 := by
  have hshape :
      4*stableCore m+1 =
        2*ternaryOnes m+3^m*(1+4*14049) := by
    unfold stableCore
    have h := ternaryOnes_identity m
    omega
  have hlo : 2*ternaryOnes m<3^m := by
    have h := ternaryOnes_identity m
    omega
  unfold digit3
  rw [hshape]
  rw [show 3^(m+8)=3^m*3^8 by rw [pow_add],
      ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt hlo]
  norm_num

/-- New unconditional, source-specific original CommonTwo for all
unbounded all-one exponent lengths m>=8, exact row m+9. -/
theorem commonTwo_allones_at_m_plus_nine
    (m : Nat) (hm : 8 ≤ m) :
    CommonTwo (ternaryOnes m) := by
  have hmod := physical_affine_stableCore_mod m hm
  have hs :
      digit3 (affineOrbit (ternaryOnes m)) (m+8) = 2 := by
    have heq := digit3_eq_of_mod_next
        (affineOrbit (ternaryOnes m)) (stableCore m)
        (m+8) (by
          simpa only [show m+8+1=m+9 by omega] using hmod)
    exact heq.trans (source_stableCore_hit m)
  have hneighborMod :
      (4*affineOrbit (ternaryOnes m)+1)%3^(m+9) =
        (4*stableCore m+1)%3^(m+9) := by
    simp [Nat.add_mod, Nat.mul_mod, hmod]
  have hn :
      digit3 (affineOrbit (ternaryOnes m+1)) (m+8) = 2 := by
    rw [affineOrbit_succ]
    have heq := digit3_eq_of_mod_next
        (4*affineOrbit (ternaryOnes m)+1)
        (4*stableCore m+1) (m+8) (by
          simpa only [show m+8+1=m+9 by omega] using hneighborMod)
    exact heq.trans (neighbor_stableCore_hit m)
  refine ⟨m+9, by omega, ?_, ?_⟩
  · simpa only [show m+8+1=m+9 by omega] using
      (four_pow_digit_affine_shift (ternaryOnes m) (m+8)).trans hs
  · simpa only [show m+8+1=m+9 by omega] using
      (four_pow_digit_affine_shift (ternaryOnes m+1) (m+8)).trans hn

/-- Export the family directly into the original third-wave gate body. -/
theorem original_thirdWave_allones
    (m : Nat) (hm : 8 ≤ m) :
    GSTFourPowerThirdWave.thirdWave (ternaryOnes m) := by
  exact (GSTFourPowerThirdWave.thirdWave_iff_commonTwo _).2
    (commonTwo_allones_at_m_plus_nine m hm)

/-!
# The exact FIRST collision on the all-one exponent physical family

The earlier theorem establishes a witness at row m+9, but does not
state the first-occurrence minimality. This section derives the
complete lower-row NO-HIT certificate by the existing nine-trit
physical fixed core: the first m rows are a genuine BAD fixed-point
prefix, and the next eight affine rows are a *finite constant* check.
The strong result pins the first CommonTwo index to exactly m+9 for
every natural m>=8. It does NOT prove the general all-K gate.
-/

/-- Any two numbers congruent modulo a high ternary power have
equal digits at every strictly lower row. -/
private theorem digit3_of_big_residue
    (a b q M : Nat) (hq : q < M)
    (h : a % 3^M = b % 3^M) :
    digit3 a q = digit3 b q := by
  apply digit3_eq_of_mod_next
  have hd : 3^(q+1) ∣ 3^M :=
    Nat.pow_dvd_pow 3 (by omega)
  calc
    a % 3^(q+1) = (a % 3^M) % 3^(q+1) :=
      (Nat.mod_mod_of_dvd a hd).symm
    _ = (b % 3^M) % 3^(q+1) := by rw [h]
    _ = b % 3^(q+1) := Nat.mod_mod_of_dvd b hd

/-- Below the m-th cut, the physical stable core has literal
ternary trit 1 at every position, so NO shared-two is possible. -/
private theorem stableCore_source_one_below (m q : Nat) (hq : q < m) :
    digit3 (stableCore m) q = 1 := by
  have hdiv : 3^(q+1) ∣ 3^m :=
    Nat.pow_dvd_pow 3 (by omega)
  have hmod :
      stableCore m % 3^(q+1) =
        ternaryOnes m % 3^(q+1) := by
    unfold stableCore
    have hzero : (3^m*14049) % 3^(q+1) = 0 :=
      Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_left hdiv _)
    rw [Nat.add_mod, hzero]
    simp
  exact (digit3_eq_of_mod_next _ _ q hmod).trans
    (ternaryOnes_digit_one m q hq)

/-- Above the m-th cut, the stable source digit is one of the
digits of the exact constant 14049. -/
private theorem stableCore_source_high (m j : Nat) :
    digit3 (stableCore m) (m+j) =
      digit3 14049 j := by
  unfold digit3 stableCore
  rw [show 3^(m+j)=3^m*3^j by rw [pow_add],
      ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt (ternaryOnes_lt_pow m)]
  rfl

/-- The neighboring affine source above the cut reads the exact
constant 4*14049+1, accounting for the one-unit boundary carry. -/
private theorem stableCore_neighbor_high (m j : Nat) :
    digit3 (4*stableCore m+1) (m+j) =
      digit3 (4*14049+1) j := by
  have hshape :
      4*stableCore m+1 =
        2*ternaryOnes m + 3^m*(1+4*14049) := by
    unfold stableCore
    have h := ternaryOnes_identity m
    omega
  have hlo : 2*ternaryOnes m < 3^m := by
    have h := ternaryOnes_identity m
    omega
  unfold digit3
  rw [hshape]
  rw [show 3^(m+j)=3^m*3^j by rw [pow_add],
      ← Nat.div_div_eq_div_mul]
  rw [Nat.add_mul_div_left _ _ (by positivity : 0<3^m),
      Nat.div_eq_of_lt hlo]
  rfl

/-- Full nine-trit sharpness: rows m through m+7 of the
renormalized core are non-colliding. The row m+8 collision is
already proved above, so this captures the entire missing band. -/
private theorem stableCore_no_common_below_m_plus_eight
    (m q : Nat) (hq : q < m+8) :
    ¬ (digit3 (stableCore m) q = 2 ∧
       digit3 (4*stableCore m+1) q = 2) := by
  by_cases hlow : q < m
  · have hone := stableCore_source_one_below m q hlow
    omega
  · let j := q-m
    have hj : j < 8 := by dsimp [j]; omega
    have hqj : q = m+j := by dsimp [j]; omega
    have hfinite : ∀ i : Fin 8,
        ¬ (digit3 14049 i.val=2 ∧
           digit3 (4*14049+1) i.val=2) := by decide
    rw [hqj, stableCore_source_high, stableCore_neighbor_high]
    exact hfinite ⟨j, hj⟩

/-- The genuine exponent source and its successor inherit the
nine-trit fixed-core no-collision property simultaneously. -/
private theorem affine_allones_no_common_below_m_plus_eight
    (m q : Nat) (hm : 8 ≤ m) (hq : q < m+8) :
    ¬ (digit3 (affineOrbit (ternaryOnes m)) q=2 ∧
       digit3 (affineOrbit (ternaryOnes m+1)) q=2) := by
  have hsrc := physical_affine_stableCore_mod m hm
  have hneighbor :
      (4*affineOrbit (ternaryOnes m)+1)%3^(m+9) =
        (4*stableCore m+1)%3^(m+9) := by
    simp [Nat.add_mod, Nat.mul_mod, hsrc]
  have hs :
      digit3 (affineOrbit (ternaryOnes m)) q =
        digit3 (stableCore m) q :=
    digit3_of_big_residue _ _ q (m+9) (by omega) hsrc
  have hn :
      digit3 (affineOrbit (ternaryOnes m+1)) q =
        digit3 (4*stableCore m+1) q := by
    rw [affineOrbit_succ]
    exact digit3_of_big_residue _ _ q (m+9)
      (by omega) hneighbor
  intro hh
  exact stableCore_no_common_below_m_plus_eight m q hq
    ⟨hs.symm.trans hh.1, hn.symm.trans hh.2⟩

/-- **Sharp physical escape:** for every m>=8, the first
shared digit-two between the original powers 4^K and
4^(K+1), K=(3^m-1)/2, occurs EXACTLY at p=m+9.
The lower bound is universal in m, not a finite scan.
This is a new all-depth obstruction/escape theorem for an
infinite family of genuine natural exponents. -/
theorem allones_first_common_two_exact
    (m : Nat) (hm : 8 ≤ m) :
    (digit3 (4^(ternaryOnes m)) (m+9) = 2 ∧
     digit3 (4^((ternaryOnes m)+1)) (m+9) = 2) ∧
    (∀ p : Nat, 1 ≤ p → p < m+9 →
      ¬ (digit3 (4^(ternaryOnes m)) p = 2 ∧
         digit3 (4^((ternaryOnes m)+1)) p = 2)) := by
  have hhit := commonTwo_allones_at_m_plus_nine m hm
  obtain ⟨p0, hp0, hp0s, hp0n⟩ := hhit
  have hexact : digit3 (4^(ternaryOnes m)) (m+9) = 2 ∧
                digit3 (4^((ternaryOnes m)+1)) (m+9)=2 := by
    -- The earlier source-specific Lean theorem already builds this exact row.
    have hmod := physical_affine_stableCore_mod m hm
    have hs : digit3 (affineOrbit (ternaryOnes m)) (m+8)=2 := by
      exact (digit3_eq_of_mod_next _ _ (m+8) (by
        simpa only [show m+8+1=m+9 by omega] using hmod)).trans
        (source_stableCore_hit m)
    have hnb :
        (4*affineOrbit (ternaryOnes m)+1)%3^(m+9) =
          (4*stableCore m+1)%3^(m+9) := by
      simp [Nat.add_mod,Nat.mul_mod,hmod]
    have hn : digit3 (affineOrbit (ternaryOnes m+1)) (m+8)=2 := by
      rw [affineOrbit_succ]
      exact (digit3_eq_of_mod_next _ _ (m+8) (by
        simpa only [show m+8+1=m+9 by omega] using hnb)).trans
        (neighbor_stableCore_hit m)
    constructor
    · exact (four_pow_digit_affine_shift (ternaryOnes m) (m+8)).trans hs
    · exact (four_pow_digit_affine_shift (ternaryOnes m+1) (m+8)).trans hn
  refine ⟨hexact, ?_⟩
  intro p hp hpbound
  let q := p-1
  have hpq : p=q+1 := by dsimp [q]; omega
  have hq : q < m+8 := by dsimp [q]; omega
  have hbad := affine_allones_no_common_below_m_plus_eight m q hm hq
  rw [hpq, four_pow_digit_affine_shift (ternaryOnes m) q,
      four_pow_digit_affine_shift (ternaryOnes m+1) q]
  exact hbad

#print axioms allones_first_common_two_exact

#print axioms commonTwo_allones_at_m_plus_nine
#print axioms original_thirdWave_allones

end GSTProblem406AllOnesFirstCollision
