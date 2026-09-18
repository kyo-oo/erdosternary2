import GSTFourPowerDirectResidue243

set_option maxRecDepth 1000000
set_option maxHeartbeats 40000000

namespace GSTFourPowerDirectResidue729

open GSTFourPowerDirectResidue

/-- Exact residue classes modulo `729 = 3^6` where row six is `2` in both consecutive powers of four. Pure direct arithmetic; no navigation. -/
def RowSixClass (r : Nat) : Prop :=
  r = 8 ∨ r = 20 ∨ r = 21 ∨ r = 22 ∨ r = 23 ∨ r = 24 ∨ r = 30 ∨ r = 51 ∨ r = 55 ∨ r = 56 ∨ r = 73 ∨ r = 74 ∨ r = 79 ∨ r = 80 ∨ r = 106 ∨ r = 110 ∨ r = 111 ∨ r = 112 ∨ r = 113 ∨ r = 118 ∨ r = 127 ∨ r = 128 ∨ r = 129 ∨ r = 130 ∨ r = 131 ∨ r = 132 ∨ r = 133 ∨ r = 134 ∨ r = 135 ∨ r = 142 ∨ r = 143 ∨ r = 147 ∨ r = 150 ∨ r = 151 ∨ r = 169 ∨ r = 172 ∨ r = 173 ∨ r = 178 ∨ r = 195 ∨ r = 216 ∨ r = 217 ∨ r = 220 ∨ r = 221 ∨ r = 222 ∨ r = 227 ∨ r = 228 ∨ r = 229 ∨ r = 230 ∨ r = 231 ∨ r = 255 ∨ r = 256 ∨ r = 257 ∨ r = 258 ∨ r = 269 ∨ r = 270 ∨ r = 271 ∨ r = 288 ∨ r = 289 ∨ r = 292 ∨ r = 303 ∨ r = 330 ∨ r = 331 ∨ r = 332 ∨ r = 333 ∨ r = 339 ∨ r = 340 ∨ r = 343 ∨ r = 351 ∨ r = 358 ∨ r = 365 ∨ r = 366 ∨ r = 367 ∨ r = 368 ∨ r = 380 ∨ r = 381 ∨ r = 382 ∨ r = 398 ∨ r = 399 ∨ r = 408 ∨ r = 409 ∨ r = 410 ∨ r = 423 ∨ r = 433 ∨ r = 434 ∨ r = 452 ∨ r = 455 ∨ r = 468 ∨ r = 480 ∨ r = 485 ∨ r = 486 ∨ r = 487 ∨ r = 488 ∨ r = 489 ∨ r = 503 ∨ r = 504 ∨ r = 518 ∨ r = 524 ∨ r = 525 ∨ r = 526 ∨ r = 548 ∨ r = 549 ∨ r = 554 ∨ r = 557 ∨ r = 562 ∨ r = 563 ∨ r = 578 ∨ r = 589 ∨ r = 606 ∨ r = 631 ∨ r = 639 ∨ r = 645 ∨ r = 646 ∨ r = 662 ∨ r = 672 ∨ r = 673 ∨ r = 674 ∨ r = 679 ∨ r = 683 ∨ r = 684 ∨ r = 685 ∨ r = 688 ∨ r = 692

/-- A row-six overlap representative lifts through the exact exponent period `3^6`. -/
theorem row_six_overlap_of_mod729_residue
    (K r : Nat) (hr : K % 729 = r)
    (h0 : digit3 (4^r) 6 = 2)
    (h1 : digit3 (4^(r+1)) 6 = 2) :
    digit3 (4^K) 6 = 2 ∧ digit3 (4^(K+1)) 6 = 2 := by
  have hm := Nat.mod_add_div K 729
  rw [hr] at hm
  have hK : K = r + 3^6 * (K / 729) := by
    norm_num at hm ⊢
    omega
  have hK1 : K + 1 = (r+1) + 3^6 * (K / 729) := by omega
  constructor
  · rw [hK]
    calc
      digit3 (4^(r + 3^6 * (K / 729))) 6 = digit3 (4^r) 6 := pow4_digit_period 6 r (K / 729)
      _ = 2 := h0
  · rw [hK1]
    calc
      digit3 (4^((r+1) + 3^6 * (K / 729))) 6 = digit3 (4^(r+1)) 6 := pow4_digit_period 6 (r+1) (K / 729)
      _ = 2 := h1

/-- Complete row-six classifier for the 122 overlap residues modulo 729. -/
theorem row_six_overlap_of_mod729_classes
    (K : Nat) (hres : RowSixClass (K % 729)) :
    digit3 (4^K) 6 = 2 ∧ digit3 (4^(K+1)) 6 = 2 := by
  unfold RowSixClass at hres
  rcases hres with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals first
    | exact row_six_overlap_of_mod729_residue K 8 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 20 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 21 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 22 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 23 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 24 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 30 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 51 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 55 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 56 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 73 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 74 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 79 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 80 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 106 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 110 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 111 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 112 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 113 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 118 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 127 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 128 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 129 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 130 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 131 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 132 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 133 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 134 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 135 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 142 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 143 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 147 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 150 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 151 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 169 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 172 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 173 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 178 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 195 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 216 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 217 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 220 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 221 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 222 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 227 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 228 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 229 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 230 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 231 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 255 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 256 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 257 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 258 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 269 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 270 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 271 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 288 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 289 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 292 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 303 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 330 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 331 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 332 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 333 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 339 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 340 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 343 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 351 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 358 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 365 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 366 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 367 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 368 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 380 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 381 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 382 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 398 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 399 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 408 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 409 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 410 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 423 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 433 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 434 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 452 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 455 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 468 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 480 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 485 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 486 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 487 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 488 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 489 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 503 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 504 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 518 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 524 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 525 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 526 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 548 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 549 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 554 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 557 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 562 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 563 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 578 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 589 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 606 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 631 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 639 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 645 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 646 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 662 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 672 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 673 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 674 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 679 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 683 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 684 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 685 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 688 h (by norm_num [digit3]) (by norm_num [digit3])
    | exact row_six_overlap_of_mod729_residue K 692 h (by norm_num [digit3]) (by norm_num [digit3])

#check row_six_overlap_of_mod729_classes
#print axioms row_six_overlap_of_mod729_classes

end GSTFourPowerDirectResidue729
