import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Infinite nested 6^k world-projection tower

The Aug-17 master equation gives one exact world coefficient `K-1` for every
cardinality K, with the equal 2/3 family obtained at `K=6^k`.

To make this a genuinely nested infinite control object, choose exponent depths
`k_n = 2^n`.  Then

  6^(2^n)-1 | 6^(2^(n+1))-1.

Thus every ordinary natural has a compatible residue in every world, and the
whole infinite tower determines that natural exactly.
-/

def gstWorldDepthS (n : Nat) : Nat := 2^n

def gstWorldCardinalityS (n : Nat) : Nat := 6^(gstWorldDepthS n)

def gstWorldModulusS (n : Nat) : Nat := gstWorldCardinalityS n - 1

/-- Every world modulus is positive. -/
theorem gst_world_modulus_posS (n : Nat) : 0 < gstWorldModulusS n := by
  unfold gstWorldModulusS gstWorldCardinalityS gstWorldDepthS
  have he : 0 < 2^n := Nat.pow_pos (by decide)
  have hp : 1 < 6^(2^n) := Nat.one_lt_pow (by decide) he
  omega

/-- Consecutive world depths double. -/
theorem gst_world_depth_succS (n : Nat) :
    gstWorldDepthS (n+1) = 2 * gstWorldDepthS n := by
  unfold gstWorldDepthS
  rw [Nat.pow_succ]
  omega

/-- The next world cardinality is the square of the current one. -/
theorem gst_world_cardinality_succ_squareS (n : Nat) :
    gstWorldCardinalityS (n+1) = (gstWorldCardinalityS n)^2 := by
  unfold gstWorldCardinalityS
  rw [gst_world_depth_succS]
  rw [show 2 * gstWorldDepthS n = gstWorldDepthS n * 2 by omega,
      Nat.pow_mul]

/-- The `6^(2^n)-1` worlds form a divisibility chain. -/
theorem gst_world_modulus_dvd_succS (n : Nat) :
    gstWorldModulusS n ∣ gstWorldModulusS (n+1) := by
  let X := gstWorldCardinalityS n
  have hX : 1 ≤ X := by
    dsimp [X, gstWorldCardinalityS, gstWorldDepthS]
    positivity
  have hnext : gstWorldCardinalityS (n+1) = X^2 := by
    simpa [X] using gst_world_cardinality_succ_squareS n
  refine ⟨X + 1, ?_⟩
  unfold gstWorldModulusS
  rw [hnext]
  have hfactor : X^2 - 1 = (X - 1) * (X + 1) := by
    nlinarith
  exact hfactor.symm

/-- Divisibility through any later world. -/
theorem gst_world_modulus_dvd_of_leS
    (i j : Nat) (hij : i ≤ j) :
    gstWorldModulusS i ∣ gstWorldModulusS j := by
  induction j with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      exact dvd_refl _
  | succ j ih =>
      by_cases hieq : i = j+1
      · subst i
        exact dvd_refl _
      · have hij' : i ≤ j := by omega
        exact dvd_trans (ih hij') (gst_world_modulus_dvd_succS j)

/-- A natural is observed in world n by reduction modulo that world's exact
coefficient `6^(2^n)-1`. -/
def gstWorldFingerprintS (R n : Nat) : Nat := R % gstWorldModulusS n

/-- World fingerprints are compatible under projection down the tower. -/
theorem gst_world_fingerprint_compatibleS
    (R n : Nat) :
    gstWorldFingerprintS R (n+1) % gstWorldModulusS n =
      gstWorldFingerprintS R n := by
  unfold gstWorldFingerprintS
  exact Nat.mod_mod_of_dvd R (gst_world_modulus_dvd_succS n)

/-- Elementary growth: n+1 never exceeds 2^n at positive n. -/
theorem gst_index_le_two_powS : ∀ n : Nat, n + 1 ≤ 2^n
  | 0 => by decide
  | n+1 => by
      have ih := gst_index_le_two_powS n
      rw [Nat.pow_succ]
      omega

/-- Six-power growth dominates every linear natural ceiling. -/
theorem gst_self_plus_two_le_six_pow_succS : ∀ R : Nat, R + 2 ≤ 6^(R+1)
  | 0 => by decide
  | R+1 => by
      have ih := gst_self_plus_two_le_six_pow_succS R
      rw [show (R+1)+1 = (R+1)+1 by rfl, Nat.pow_succ]
      have hp : 0 < 6^(R+1) := Nat.pow_pos (by decide)
      omega

/-- Explicit recovery world: world `R+1` already has modulus strictly larger
than R. -/
theorem gst_lt_recovery_world_modulusS (R : Nat) :
    R < gstWorldModulusS (R+1) := by
  unfold gstWorldModulusS gstWorldCardinalityS gstWorldDepthS
  have hlin : R + 2 ≤ 6^(R+1) := gst_self_plus_two_le_six_pow_succS R
  have hexp : R + 1 ≤ 2^(R+1) := gst_index_le_two_powS (R+1)
  have hpow : 6^(R+1) ≤ 6^(2^(R+1)) :=
    Nat.pow_le_pow_of_le (by decide : 1 < 6) hexp
  omega

/-- The infinite tower fingerprint is injective on ordinary naturals. -/
theorem gst_world_fingerprint_injectiveS
    (R S : Nat)
    (hfp : ∀ n, gstWorldFingerprintS R n = gstWorldFingerprintS S n) :
    R = S := by
  let B := R + S
  let n := B + 1
  have hB : B < gstWorldModulusS n := by
    simpa [n] using gst_lt_recovery_world_modulusS B
  have hR : R < gstWorldModulusS n := by
    dsimp [B] at hB
    omega
  have hS : S < gstWorldModulusS n := by
    dsimp [B] at hB
    omega
  have h := hfp n
  unfold gstWorldFingerprintS at h
  rw [Nat.mod_eq_of_lt hR, Nat.mod_eq_of_lt hS] at h
  exact h

/-- A compatible world-tower state. -/
structure GSTWorldTowerStateS where
  residue : Nat → Nat
  legal : ∀ n, residue n < gstWorldModulusS n
  compatible : ∀ n,
    residue (n+1) % gstWorldModulusS n = residue n

/-- Every ordinary natural embeds into the infinite tower. -/
def gstWorldTowerOfNatS (R : Nat) : GSTWorldTowerStateS where
  residue := gstWorldFingerprintS R
  legal := by
    intro n
    unfold gstWorldFingerprintS
    exact Nat.mod_lt _ (gst_world_modulus_posS n)
  compatible := gst_world_fingerprint_compatibleS R

/-- The infinite tower embedding of naturals is injective. -/
theorem gst_world_tower_of_nat_injectiveS
    (R S : Nat)
    (h : gstWorldTowerOfNatS R = gstWorldTowerOfNatS S) :
    R = S := by
  apply gst_world_fingerprint_injectiveS R S
  intro n
  have hr := congrArg (fun w : GSTWorldTowerStateS => w.residue n) h
  exact hr

/-- If a finite natural looks zero in every world, the infinite tower forces it
to be literally zero. -/
theorem gst_world_zero_shadow_forces_zeroS
    (R : Nat)
    (hzero : ∀ n, gstWorldFingerprintS R n = 0) :
    R = 0 := by
  apply gst_world_fingerprint_injectiveS R 0
  intro n
  rw [hzero n]
  unfold gstWorldFingerprintS
  simp

/-- The global `I != BIG1` branch is the maximal world coefficient at every
tower depth. -/
theorem gst_big1_clear_world_tower_maximalS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ n,
      gstBig1ProjectedPathCodeS a d (gstWorldDepthS n) =
        gstWorldModulusS n := by
  intro n
  have h := gst_big1_clear_infinite_all_six_prefixes_maximalS
    a d hpath h0 (gstWorldDepthS n)
  simpa [gstWorldModulusS, gstWorldCardinalityS] using h

/-- Therefore the no-BIG1 path casts a zero residue shadow in every nested
world. -/
theorem gst_big1_clear_world_tower_zero_shadowS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0) :
    ∀ n,
      gstBig1ProjectedPathCodeS a d (gstWorldDepthS n) %
        gstWorldModulusS n = 0 := by
  intro n
  rw [gst_big1_clear_world_tower_maximalS a d hpath h0 n]
  exact Nat.mod_self _

/-- Infinite-control collision theorem.  Suppose one fixed conserved natural
information value I has, in every nested 6^k world, the same residue as the
no-BIG1 microscopic path.  The infinite tower forces I=0. -/
theorem gst_big1_clear_fixed_information_forced_zeroS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (I : Nat)
    (hprojection : ∀ n,
      gstWorldFingerprintS I n =
        gstBig1ProjectedPathCodeS a d (gstWorldDepthS n) %
          gstWorldModulusS n) :
    I = 0 := by
  apply gst_world_zero_shadow_forces_zeroS I
  intro n
  rw [hprojection n,
    gst_big1_clear_world_tower_zero_shadowS a d hpath h0 n]

/-- Nonzero fixed conserved information cannot agree with a global no-BIG1
path in every world.  This is the direct infinite contradiction interface for
the physical/canonical adapter. -/
theorem gst_big1_clear_nonzero_fixed_information_impossibleS
    (a d : Nat → Nat)
    (hpath : GSTBig1ClearInfinitePathS a d)
    (h0 : d 0 ≠ 0)
    (I : Nat) (hI : I ≠ 0)
    (hprojection : ∀ n,
      gstWorldFingerprintS I n =
        gstBig1ProjectedPathCodeS a d (gstWorldDepthS n) %
          gstWorldModulusS n) : False := by
  exact hI (gst_big1_clear_fixed_information_forced_zeroS
    a d hpath h0 I hprojection)

end GSTInfiniteV2
