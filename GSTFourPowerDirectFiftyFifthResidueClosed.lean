import GSTFourPowerDirectResidue

set_option maxRecDepth 1000000
set_option maxHeartbeats 30000000

namespace GSTFourPowerDirectFiftyFifthResidueClosed

open GSTFourPowerDirectResidue

private theorem pow4_85117_mod56 :
    4 ^ 85117 % 523347633027360537213511521 = 372058536685824102516440692 := by
  have hp0 : 4 ^ 1 % 523347633027360537213511521 = 4 := by norm_num
  have hp1 : 4 ^ 2 % 523347633027360537213511521 = 16 := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, pow_add, Nat.mul_mod, hp0]
  have hp2 : 4 ^ 4 % 523347633027360537213511521 = 256 := by
    rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add, Nat.mul_mod, hp1]
  have hp3 : 4 ^ 8 % 523347633027360537213511521 = 65536 := by
    rw [show (8 : Nat) = 4 + 4 by norm_num, pow_add, Nat.mul_mod, hp2]
  have hp4 : 4 ^ 16 % 523347633027360537213511521 = 4294967296 := by
    rw [show (16 : Nat) = 8 + 8 by norm_num, pow_add, Nat.mul_mod, hp3]
  have hp5 : 4 ^ 32 % 523347633027360537213511521 = 18446744073709551616 := by
    rw [show (32 : Nat) = 16 + 16 by norm_num, pow_add, Nat.mul_mod, hp4]
  have hp6 : 4 ^ 64 % 523347633027360537213511521 = 243709935177737525112446170 := by
    rw [show (64 : Nat) = 32 + 32 by norm_num, pow_add, Nat.mul_mod, hp5]
  have hp7 : 4 ^ 128 % 523347633027360537213511521 = 397257593673184439192653732 := by
    rw [show (128 : Nat) = 64 + 64 by norm_num, pow_add, Nat.mul_mod, hp6]
  have hp8 : 4 ^ 256 % 523347633027360537213511521 = 233465874074786490330636472 := by
    rw [show (256 : Nat) = 128 + 128 by norm_num, pow_add, Nat.mul_mod, hp7]
  have hp9 : 4 ^ 512 % 523347633027360537213511521 = 402111618988039266785989345 := by
    rw [show (512 : Nat) = 256 + 256 by norm_num, pow_add, Nat.mul_mod, hp8]
  have hp10 : 4 ^ 1024 % 523347633027360537213511521 = 164887084036508799186479659 := by
    rw [show (1024 : Nat) = 512 + 512 by norm_num, pow_add, Nat.mul_mod, hp9]
  have hp11 : 4 ^ 2048 % 523347633027360537213511521 = 77587068145980047908761961 := by
    rw [show (2048 : Nat) = 1024 + 1024 by norm_num, pow_add, Nat.mul_mod, hp10]
  have hp12 : 4 ^ 4096 % 523347633027360537213511521 = 221443753572513265731247039 := by
    rw [show (4096 : Nat) = 2048 + 2048 by norm_num, pow_add, Nat.mul_mod, hp11]
  have hp13 : 4 ^ 8192 % 523347633027360537213511521 = 101812535618617067465538745 := by
    rw [show (8192 : Nat) = 4096 + 4096 by norm_num, pow_add, Nat.mul_mod, hp12]
  have hp14 : 4 ^ 16384 % 523347633027360537213511521 = 183874064143050173931413098 := by
    rw [show (16384 : Nat) = 8192 + 8192 by norm_num, pow_add, Nat.mul_mod, hp13]
  have hp15 : 4 ^ 32768 % 523347633027360537213511521 = 55309892918356031316180784 := by
    rw [show (32768 : Nat) = 16384 + 16384 by norm_num, pow_add, Nat.mul_mod, hp14]
  have hp16 : 4 ^ 65536 % 523347633027360537213511521 = 181847893174614252955405939 := by
    rw [show (65536 : Nat) = 32768 + 32768 by norm_num, pow_add, Nat.mul_mod, hp15]
  have hc1 : 4 ^ 1 % 523347633027360537213511521 = 4 := hp0
  have hc5 : 4 ^ 5 % 523347633027360537213511521 = 1024 := by
    rw [show (5 : Nat) = 1 + 4 by norm_num, pow_add, Nat.mul_mod, hc1, hp2]
  have hc13 : 4 ^ 13 % 523347633027360537213511521 = 67108864 := by
    rw [show (13 : Nat) = 5 + 8 by norm_num, pow_add, Nat.mul_mod, hc5, hp3]
  have hc29 : 4 ^ 29 % 523347633027360537213511521 = 288230376151711744 := by
    rw [show (29 : Nat) = 13 + 16 by norm_num, pow_add, Nat.mul_mod, hc13, hp4]
  have hc61 : 4 ^ 61 % 523347633027360537213511521 = 314545624847147467800404437 := by
    rw [show (61 : Nat) = 29 + 32 by norm_num, pow_add, Nat.mul_mod, hc29, hp5]
  have hc125 : 4 ^ 125 % 523347633027360537213511521 = 235171739350613741893296505 := by
    rw [show (125 : Nat) = 61 + 64 by norm_num, pow_add, Nat.mul_mod, hc61, hp6]
  have hc1149 : 4 ^ 1149 % 523347633027360537213511521 = 411747270267327091167603079 := by
    rw [show (1149 : Nat) = 125 + 1024 by norm_num, pow_add, Nat.mul_mod, hc125, hp10]
  have hc3197 : 4 ^ 3197 % 523347633027360537213511521 = 190439461739359970523919843 := by
    rw [show (3197 : Nat) = 1149 + 2048 by norm_num, pow_add, Nat.mul_mod, hc1149, hp11]
  have hc19581 : 4 ^ 19581 % 523347633027360537213511521 = 306496927289492247468142378 := by
    rw [show (19581 : Nat) = 3197 + 16384 by norm_num, pow_add, Nat.mul_mod, hc3197, hp14]
  have hc85117 : 4 ^ 85117 % 523347633027360537213511521 = 372058536685824102516440692 := by
    rw [show (85117 : Nat) = 19581 + 65536 by norm_num, pow_add, Nat.mul_mod, hc19581, hp16]
  exact hc85117

private theorem pow4_85118_mod56 :
    4 ^ 85118 % 523347633027360537213511521 = 441538880688575335638739726 := by
  have hp0 : 4 ^ 1 % 523347633027360537213511521 = 4 := by norm_num
  have hp1 : 4 ^ 2 % 523347633027360537213511521 = 16 := by
    rw [show (2 : Nat) = 1 + 1 by norm_num, pow_add, Nat.mul_mod, hp0]
  have hp2 : 4 ^ 4 % 523347633027360537213511521 = 256 := by
    rw [show (4 : Nat) = 2 + 2 by norm_num, pow_add, Nat.mul_mod, hp1]
  have hp3 : 4 ^ 8 % 523347633027360537213511521 = 65536 := by
    rw [show (8 : Nat) = 4 + 4 by norm_num, pow_add, Nat.mul_mod, hp2]
  have hp4 : 4 ^ 16 % 523347633027360537213511521 = 4294967296 := by
    rw [show (16 : Nat) = 8 + 8 by norm_num, pow_add, Nat.mul_mod, hp3]
  have hp5 : 4 ^ 32 % 523347633027360537213511521 = 18446744073709551616 := by
    rw [show (32 : Nat) = 16 + 16 by norm_num, pow_add, Nat.mul_mod, hp4]
  have hp6 : 4 ^ 64 % 523347633027360537213511521 = 243709935177737525112446170 := by
    rw [show (64 : Nat) = 32 + 32 by norm_num, pow_add, Nat.mul_mod, hp5]
  have hp7 : 4 ^ 128 % 523347633027360537213511521 = 397257593673184439192653732 := by
    rw [show (128 : Nat) = 64 + 64 by norm_num, pow_add, Nat.mul_mod, hp6]
  have hp8 : 4 ^ 256 % 523347633027360537213511521 = 233465874074786490330636472 := by
    rw [show (256 : Nat) = 128 + 128 by norm_num, pow_add, Nat.mul_mod, hp7]
  have hp9 : 4 ^ 512 % 523347633027360537213511521 = 402111618988039266785989345 := by
    rw [show (512 : Nat) = 256 + 256 by norm_num, pow_add, Nat.mul_mod, hp8]
  have hp10 : 4 ^ 1024 % 523347633027360537213511521 = 164887084036508799186479659 := by
    rw [show (1024 : Nat) = 512 + 512 by norm_num, pow_add, Nat.mul_mod, hp9]
  have hp11 : 4 ^ 2048 % 523347633027360537213511521 = 77587068145980047908761961 := by
    rw [show (2048 : Nat) = 1024 + 1024 by norm_num, pow_add, Nat.mul_mod, hp10]
  have hp12 : 4 ^ 4096 % 523347633027360537213511521 = 221443753572513265731247039 := by
    rw [show (4096 : Nat) = 2048 + 2048 by norm_num, pow_add, Nat.mul_mod, hp11]
  have hp13 : 4 ^ 8192 % 523347633027360537213511521 = 101812535618617067465538745 := by
    rw [show (8192 : Nat) = 4096 + 4096 by norm_num, pow_add, Nat.mul_mod, hp12]
  have hp14 : 4 ^ 16384 % 523347633027360537213511521 = 183874064143050173931413098 := by
    rw [show (16384 : Nat) = 8192 + 8192 by norm_num, pow_add, Nat.mul_mod, hp13]
  have hp15 : 4 ^ 32768 % 523347633027360537213511521 = 55309892918356031316180784 := by
    rw [show (32768 : Nat) = 16384 + 16384 by norm_num, pow_add, Nat.mul_mod, hp14]
  have hp16 : 4 ^ 65536 % 523347633027360537213511521 = 181847893174614252955405939 := by
    rw [show (65536 : Nat) = 32768 + 32768 by norm_num, pow_add, Nat.mul_mod, hp15]
  have hc2 : 4 ^ 2 % 523347633027360537213511521 = 16 := hp1
  have hc6 : 4 ^ 6 % 523347633027360537213511521 = 4096 := by
    rw [show (6 : Nat) = 2 + 4 by norm_num, pow_add, Nat.mul_mod, hc2, hp2]
  have hc14 : 4 ^ 14 % 523347633027360537213511521 = 268435456 := by
    rw [show (14 : Nat) = 6 + 8 by norm_num, pow_add, Nat.mul_mod, hc6, hp3]
  have hc30 : 4 ^ 30 % 523347633027360537213511521 = 1152921504606846976 := by
    rw [show (30 : Nat) = 14 + 16 by norm_num, pow_add, Nat.mul_mod, hc14, hp4]
  have hc62 : 4 ^ 62 % 523347633027360537213511521 = 211487233333868796774594706 := by
    rw [show (62 : Nat) = 30 + 32 by norm_num, pow_add, Nat.mul_mod, hc30, hp5]
  have hc126 : 4 ^ 126 % 523347633027360537213511521 = 417339324375094430359674499 := by
    rw [show (126 : Nat) = 62 + 64 by norm_num, pow_add, Nat.mul_mod, hc62, hp6]
  have hc1150 : 4 ^ 1150 % 523347633027360537213511521 = 76946181987226753029877753 := by
    rw [show (1150 : Nat) = 126 + 1024 by norm_num, pow_add, Nat.mul_mod, hc126, hp10]
  have hc3198 : 4 ^ 3198 % 523347633027360537213511521 = 238410213930079344882167851 := by
    rw [show (3198 : Nat) = 1150 + 2048 by norm_num, pow_add, Nat.mul_mod, hc1150, hp11]
  have hc19582 : 4 ^ 19582 % 523347633027360537213511521 = 179292443103247915445546470 := by
    rw [show (19582 : Nat) = 3198 + 16384 by norm_num, pow_add, Nat.mul_mod, hc3198, hp14]
  have hc85118 : 4 ^ 85118 % 523347633027360537213511521 = 441538880688575335638739726 := by
    rw [show (85118 : Nat) = 19582 + 65536 by norm_num, pow_add, Nat.mul_mod, hc19582, hp16]
  exact hc85118

theorem row55_reference_closed :
    digit3 (4 ^ 85117) 55 = 2 ∧ digit3 (4 ^ 85118) 55 = 2 := by
  have hM : 3 ^ (55 + 1) = 523347633027360537213511521 := by norm_num
  constructor
  · have hmod : 4 ^ 85117 % 3 ^ (55 + 1) = 372058536685824102516440692 := by
      rw [hM]
      exact pow4_85117_mod56
    have hEq : digit3 (4 ^ 85117) 55 = digit3 372058536685824102516440692 55 := by
      apply digit3_eq_of_mod_next
      rw [hmod]
      norm_num [hM]
    rw [hEq]
    norm_num [digit3]
  · have hmod : 4 ^ 85118 % 3 ^ (55 + 1) = 441538880688575335638739726 := by
      rw [hM]
      exact pow4_85118_mod56
    have hEq : digit3 (4 ^ 85118) 55 = digit3 441538880688575335638739726 55 := by
      apply digit3_eq_of_mod_next
      rw [hmod]
      norm_num [hM]
    rw [hEq]
    norm_num [digit3]

#check row55_reference_closed

end GSTFourPowerDirectFiftyFifthResidueClosed
