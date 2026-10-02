import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

namespace GSTFourPowerDirectResidue243

open GSTFourPowerDirectResidue

/-- Exact residue classes modulo `243 = 3^5` where row five is `2` in
both consecutive powers of four.  Pure direct arithmetic; no navigation. -/
def RowFiveClass (r : Nat) : Prop :=
  r = 19 ∨ r = 20 ∨ r = 21 ∨ r = 38 ∨ r = 45 ∨ r = 48 ∨ r = 61 ∨ r = 70 ∨
  r = 71 ∨ r = 72 ∨ r = 73 ∨ r = 76 ∨ r = 77 ∨ r = 78 ∨ r = 85 ∨ r = 86 ∨
  r = 87 ∨ r = 90 ∨ r = 91 ∨ r = 114 ∨ r = 115 ∨ r = 116 ∨ r = 117 ∨ r = 122 ∨
  r = 123 ∨ r = 124 ∨ r = 133 ∨ r = 134 ∨ r = 138 ∨ r = 145 ∨ r = 146 ∨
  r = 162 ∨ r = 163 ∨ r = 164 ∨ r = 174 ∨ r = 175 ∨ r = 179 ∨ r = 185 ∨
  r = 221 ∨ r = 229

/-- A row-five overlap representative lifts through the exact exponent period `3^5`. -/
theorem row_five_overlap_of_mod243_residue
    (K r : Nat) (hr : K % 243 = r)
    (h0 : digit3 (4^r) 5 = 2)
    (h1 : digit3 (4^(r+1)) 5 = 2) :
    digit3 (4^K) 5 = 2 ∧ digit3 (4^(K+1)) 5 = 2 := by
  have hm := Nat.mod_add_div K 243
  rw [hr] at hm
  have hK : K = r + 3^5 * (K / 243) := by
    norm_num at hm ⊢
    omega
  have hK1 : K + 1 = (r+1) + 3^5 * (K / 243) := by omega
  constructor
  · rw [hK]
    calc
      digit3 (4^(r + 3^5 * (K / 243))) 5 = digit3 (4^r) 5 := pow4_digit_period 5 r (K / 243)
      _ = 2 := h0
  · rw [hK1]
    calc
      digit3 (4^((r+1) + 3^5 * (K / 243))) 5 = digit3 (4^(r+1)) 5 := pow4_digit_period 5 (r+1) (K / 243)
      _ = 2 := h1

/-- Complete row-five classifier for the forty overlap residues modulo 243. -/
theorem row_five_overlap_of_mod243_classes
    (K : Nat) (hres : RowFiveClass (K % 243)) :
    digit3 (4^K) 5 = 2 ∧ digit3 (4^(K+1)) 5 = 2 := by
  unfold RowFiveClass at hres
  rcases hres with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals first
    | exact row_five_overlap_of_mod243_residue K 19 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 20 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 21 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 38 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 45 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 48 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 61 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 70 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 71 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 72 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 73 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 76 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 77 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 78 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 85 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 86 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 87 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 90 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 91 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 114 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 115 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 116 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 117 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 122 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 123 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 124 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 133 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 134 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 138 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 145 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 146 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 162 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 163 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 164 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 174 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 175 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 179 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 185 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 221 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_five_overlap_of_mod243_residue K 229 h (by norm_num [digit3]) (by norm_num [digit3])

#check row_five_overlap_of_mod243_classes
#print axioms row_five_overlap_of_mod243_classes

end GSTFourPowerDirectResidue243
