import GSTGraphV2InfiniteControlScratch

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace GSTInfiniteV2

/-!
# Exact cardinal-world master equation

This is the integer-cleared form of the handwritten world projection

    4 D_R(3/K) - E_R(3/K) = (K-1) C_R(3/K).

Rather than use rational functions, we recursively clear the K-denominators.
The theorem is exact over Nat.  The coefficient K-1 therefore exists for every
world cardinality K simultaneously.
-/

def gstOutputDigitS (R p : Nat) : Nat :=
  (gstCarryS R p + 4 * gstDigitS R p) % 3

theorem gst_cell_conservation_cardinalS (R p : Nat) :
    gstCarryS R p + 4 * gstDigitS R p =
      gstOutputDigitS R p + 3 * gstCarryS R (p+1) := by
  have hcarry := gstCarryS_forward_exact_all R p
  unfold gstOutputDigitS
  rw [hcarry]
  unfold gstStepCarryS
  have h := Nat.mod_add_div
    (gstCarryS R p + 4 * gstDigitS R p) 3
  omega

def gstCardinalInputEvalS (R K : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
      K * gstCardinalInputEvalS R K L +
        K * 3^L * gstDigitS R L

def gstCardinalOutputEvalS (R K : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
      K * gstCardinalOutputEvalS R K L +
        K * 3^L * gstOutputDigitS R L

def gstCardinalCarryEvalS (R K : Nat) : Nat → Nat
  | 0 => 0
  | L+1 =>
      K * gstCardinalCarryEvalS R K L +
        3^(L+1) * gstCarryS R (L+1)

theorem gst_cardinal_master_with_boundaryS
    (R K L : Nat) :
    4 * gstCardinalInputEvalS R K L +
        gstCardinalCarryEvalS R K L =
      gstCardinalOutputEvalS R K L +
        K * gstCardinalCarryEvalS R K L +
        3^L * gstCarryS R L := by
  induction L with
  | zero =>
      simp [gstCardinalInputEvalS, gstCardinalOutputEvalS,
        gstCardinalCarryEvalS, gstCarryS, Nat.mod_one]
  | succ L ih =>
      have hlocal := gst_cell_conservation_cardinalS R L
      rw [gstCardinalInputEvalS, gstCardinalOutputEvalS,
        gstCardinalCarryEvalS]
      calc
        4 * (K * gstCardinalInputEvalS R K L +
              K * 3^L * gstDigitS R L) +
            (K * gstCardinalCarryEvalS R K L +
              3^(L+1) * gstCarryS R (L+1)) =
          K * (4 * gstCardinalInputEvalS R K L +
              gstCardinalCarryEvalS R K L) +
            K * 3^L * (4 * gstDigitS R L) +
            3^(L+1) * gstCarryS R (L+1) := by ring
        _ = K * (gstCardinalOutputEvalS R K L +
              K * gstCardinalCarryEvalS R K L +
              3^L * gstCarryS R L) +
            K * 3^L * (4 * gstDigitS R L) +
            3^(L+1) * gstCarryS R (L+1) := by rw [ih]
        _ = K * gstCardinalOutputEvalS R K L +
            K * K * gstCardinalCarryEvalS R K L +
            K * 3^L *
              (gstCarryS R L + 4 * gstDigitS R L) +
            3^(L+1) * gstCarryS R (L+1) := by ring
        _ = K * gstCardinalOutputEvalS R K L +
            K * K * gstCardinalCarryEvalS R K L +
            K * 3^L *
              (gstOutputDigitS R L + 3 * gstCarryS R (L+1)) +
            3^(L+1) * gstCarryS R (L+1) := by rw [hlocal]
        _ = (K * gstCardinalOutputEvalS R K L +
              K * 3^L * gstOutputDigitS R L) +
            K * (K * gstCardinalCarryEvalS R K L +
              3^(L+1) * gstCarryS R (L+1)) +
            3^(L+1) * gstCarryS R (L+1) := by
              rw [Nat.pow_succ]
              ring

theorem gst_four_mul_self_lt_three_pow_succS :
    ∀ R : Nat, 4*R < 3^(R+1)
  | 0 => by decide
  | R+1 => by
      have ih : 4*R < 3^(R+1) :=
        gst_four_mul_self_lt_three_pow_succS R
      have hp : 2 ≤ 3^(R+1) := by
        have hpos : 0 < 3^R := Nat.pow_pos (by decide)
        rw [Nat.pow_succ]
        omega
      rw [show (R+1)+1 = (R+1)+1 by rfl, Nat.pow_succ]
      omega

theorem gst_carry_zero_at_natural_ceilingS (R : Nat) :
    gstCarryS R (R+1) = 0 := by
  unfold gstCarryS
  have hR : R < 3^(R+1) := gst_self_lt_three_pow_succS R
  rw [Nat.mod_eq_of_lt hR]
  exact Nat.div_eq_of_lt (gst_four_mul_self_lt_three_pow_succS R)

theorem gst_cardinal_master_exactS
    (R K : Nat) (hK : 1 ≤ K) :
    4 * gstCardinalInputEvalS R K (R+1) =
      gstCardinalOutputEvalS R K (R+1) +
        (K-1) * gstCardinalCarryEvalS R K (R+1) := by
  have h := gst_cardinal_master_with_boundaryS R K (R+1)
  rw [gst_carry_zero_at_natural_ceilingS, Nat.mul_zero, Nat.add_zero] at h
  let C := gstCardinalCarryEvalS R K (R+1)
  have hKshape : K = 1 + (K-1) := by omega
  have hmul : K * C = C + (K-1) * C := by
    calc
      K * C = (1 + (K-1)) * C := by rw [hKshape]
      _ = C + (K-1) * C := by ring
  dsimp only [C] at hmul
  rw [hmul] at h
  omega

theorem gst_cardinal_master_sixS (R : Nat) :
    4 * gstCardinalInputEvalS R 6 (R+1) =
      gstCardinalOutputEvalS R 6 (R+1) +
        5 * gstCardinalCarryEvalS R 6 (R+1) := by
  simpa using gst_cardinal_master_exactS R 6 (by decide)

theorem gst_cardinal_master_eight_factor_sevenS (R : Nat) :
    4 * gstCardinalInputEvalS R 8 (R+1) =
      gstCardinalOutputEvalS R 8 (R+1) +
        7 * gstCardinalCarryEvalS R 8 (R+1) := by
  simpa using gst_cardinal_master_exactS R 8 (by decide)

theorem gst_cardinal_master_twelve_factor_elevenS (R : Nat) :
    4 * gstCardinalInputEvalS R 12 (R+1) =
      gstCardinalOutputEvalS R 12 (R+1) +
        11 * gstCardinalCarryEvalS R 12 (R+1) := by
  simpa using gst_cardinal_master_exactS R 12 (by decide)

theorem gst_cardinal_master_thirtysix_factor_thirtyfiveS (R : Nat) :
    4 * gstCardinalInputEvalS R 36 (R+1) =
      gstCardinalOutputEvalS R 36 (R+1) +
        35 * gstCardinalCarryEvalS R 36 (R+1) := by
  simpa using gst_cardinal_master_exactS R 36 (by decide)

theorem gst_cardinal_master_six_powS
    (R q : Nat) :
    4 * gstCardinalInputEvalS R (6^q) (R+1) =
      gstCardinalOutputEvalS R (6^q) (R+1) +
        (6^q-1) * gstCardinalCarryEvalS R (6^q) (R+1) := by
  have hKpos : 0 < 6^q := Nat.pow_pos (by decide)
  have hK : 1 ≤ 6^q := by omega
  exact gst_cardinal_master_exactS R (6^q) hK

def GSTInfiniteCardinalMasterS (R : Nat) : Prop :=
  ∀ K, 1 ≤ K →
    4 * gstCardinalInputEvalS R K (R+1) =
      gstCardinalOutputEvalS R K (R+1) +
        (K-1) * gstCardinalCarryEvalS R K (R+1)

theorem gst_infinite_cardinal_masterS
    (R : Nat) : GSTInfiniteCardinalMasterS R := by
  intro K hK
  exact gst_cardinal_master_exactS R K hK

end GSTInfiniteV2
