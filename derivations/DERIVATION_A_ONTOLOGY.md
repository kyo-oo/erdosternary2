# DERIVATION — LANE A_ONTOLOGY (the monolith's own universe)
# Erdős Ternary Campaign · Task ID 9-a · Agent: opus-A_ONTOLOGY
# Branch sol/kyo-gate-universe-wire · Clone /home/z/erdosternary2

Files read this session (every citation below comes from these reads):
`ErdosTernary2.lean` (18,527 lines; structure sweep + targeted chunks),
`GSTGraphV2OmegaWaveLaw.lean` (FULL, 3,042 lines), `GSTCanonicalTailStateIso.lean` (FULL),
`GSTCanonicalCarryDynamics.lean` (FULL), `GSTCanonicalEnergyControl.lean` (FULL),
`GSTCanonicalBoundaryRigidity.lean` (FULL), `GSTCanonicalFirstGateControl.lean` (FULL),
`GSTCanonicalFirstGateStandalone.lean` (FULL), `GST2DMixedEmergence.lean` (FULL),
`GSTCanonicalTailEscapeAudit.lean` (FULL), `CAMPAIGN_BRIEF.md`.

---

## §1 THE TARGET (verbatim)

Lane A attacks the monolith's own terminal face of the ONE Prop — the kill-all form that
§7.15 of the monolith certifies as the fixed point (ErdosTernary2.lean:18425-18427):

```lean
theorem erdos_even_conjecture_iff_tailF :
    (∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false)
      ↔ GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF := by
```

i.e. the even half of Erdős ternary: **the only powers of 4 with no ternary digit 2 are
4^0 = 1, 4^1 = 4, 4^4 = 256** (equivalently `∀ K ≥ 8, ∃ p, digit3 (4^K) p = 2`, the
left side of `omega_shadow_kill_all_of_closed`, ErdosTernary2.lean:18394-18396). The six
green-equivalent forms are inter-derivable (brief §1; ban 8 — not re-litigated).

The lane mission: extract every unconditional digit-2-forcing law in the monolith's
ontology (GST v2 graph universe, omega wave incl. §7.13 tower observer / §7.14 row
observer, first gates, energy control, boundary rigidity), build the coverage map over
K ≥ 8, attempt the assembly, and either complete it or name the exact gap.

---

## §2 GREEN INVENTORY (every law used, file:line, one line each)

### Ω-wave law file (GSTGraphV2OmegaWaveLaw.lean — "the Law")

- `omegaWaveStep` :88 — the Ω-wave transfusion operator `(D,X) ↦ ((D+4·trit X)/3, X/3)`.
- `omegaWaveStep_worldtrace` :119 — the operator's orbit IS the carry stream of any energy
  (`(omegaWaveStep (carry4 R p) (R/3^p)).1 = carry4 R (p+1)`), the worldtrace law.
- `omega_cut_factor` :145 — **exact**: `4^(3^a·core) = 1 + 3^(a+1) · omegaCutWord a core`.
- `omega_cut_digit` :187 — `digit3 (4^(3^a·core)) (a+1) = core % 3` (UNCONDITIONAL).
- `omega_cut_prefix_one` :205 — `4^(3^a·core) % 3^(a+1) = 1`.
- `omega_cut_carry_zero` :211 — cut carry is 0 for `a ≥ 1`.
- `omega_cut_happy_gate` :228 — core ≡ 2 (mod 3), a ≥ 1 → HappyCell at row a+1 (UNCOND.).
- `omega_lteCoeff_mod9` :240 — `lteCoeff a % 9 = 7` for a ≥ 1.
- `omega_level2_digit_two` :335 — s ≥ 1, core ∈ {1,5,6} mod 9 → digit 2 at row s+2 (UNCOND.).
- `omega_lteCoeff_stable` :395 — tower stabilization: `lteCoeff ((L−1)+d) % 3^L` constant.
- `omega_row2_digit_two` :582 — K ≡ 7 (mod 9) → digit 2 at row 2 (its proof fixes
  `4^9 % 27 = 1`, `4^7 % 27 = 22`, :587-588).
- `omega_three_free_decomposition` :598 — every K > 0 is `3^s · core`, 3 ∤ core.
- `omegaShadow` :617 — the shadow residue: core ≡ 4 (mod 9) any s; (s=0, core ≡ 1 mod 9);
  (s ≥ 1, core ≡ 7 mod 9).
- `four_power_omega_shadow_wave` :625 — **DEF (input)**: every shadow K ≥ 8 owns digit 2.
- `omega_digit_two_cases` :631 — K ≥ 8 → `omegaShadow K ∨ ∃ p, digit3 (4^K) p = 2` (UNCOND.).
- `omega_digit_two_of_not_shadow` :659 — non-shadow K ≥ 8 owns digit 2 (UNCONDITIONAL).
- `omega_digit_two_coverage` :666 — under the shadow-wave input, every K ≥ 8 owns digit 2.
- `omega_level3_digit_two` :746 — s ≥ 2, core ≡ 13,25 (mod 27) → row s+3.
- `omega_cut_word_full` :800 — cut word mod 3^(s+2) = `lteCoeff s·core + 3^(s+1)·lteCoeff²·C(core,2)`.
- `omega_cut_word_mod_pow2` :858 — core ≡ 1 (mod 3) → `omegaCutWord s core ≡ lteCoeff s·core (mod 3^(s+2))`.
- `digit3_window` :901 — `(X/3^j)%3 = (X % 3^(j+1))/3^j`.
- `omega_sheet_digit` :931 / `omega_sheet_gate_digit_two` :953 — row 2s+2 gate (top trit of
  the sheet-local word mod the squared cut modulus).
- `omega_level4_digit_two` :1047 — s ≥ 3, `(16·core)%81 ≥ 54` → row s+4.
- `omega_cut_word_full3` :1178 — cut word mod 3^(s+3) to second binomial order.
- `omega_sheet2_gate_four` :1258 — s ≥ 1, core ≡ 4 (mod 9), sheet word in lowest third → row 2s+3.
- `omega_sheet2_gate_seven` :1307 — s ≥ 1, core ≡ 7 (mod 9), sheet word in middle third → row 2s+3.
- `omega_expcycle_row3_digit_two` :1393 — K ≡ 19,22 (mod 27) → row 3 (period 27/81 law).
- `omega_expcycle_row4_digit_two_one` :1424 / `_four` :1480 — K ≡ 55,64,73 / 58,67,76 (mod 81) → row 4.
- `omega_level5_digit_two` :1618 — s ≥ 4, `(178·core)%243 ≥ 162` → row s+5.
- `omega_level6_digit_two` :1697 — s ≥ 5, `(664·core)%729 ≥ 486` → row s+6.
- `omega_expcycle_row5_digit_two_one` :1726 / `_four` :1797 — 8 classes mod 243 → row 5.
- `omega_level7_digit_two` :1971 — s ≥ 6, `(664·core)%2187 ≥ 1458` → row s+7.
- `omega_expcycle_row6_digit_two_one` :1992 / `_four` :2087 — 16 classes mod 729 → row 6.
- `omega_tripling_cut_word` :2343 — exact cube recurrence of the cut word across sheets.
- `omega_tripling_digit_transfer` :2401 — cross-sheet: child row 2s+3 = parent row 2s+2 + 1 (mod 3).
- `omega_tripling_gate` :2474 / `omega_tripling_child_digit_two` :2482 — parent sheet-gate trit 1 → child digit 2.
- `graph_column_digit_exact` :2514 — the infinite control graph's digit cell IS `digit3 (4^t·E) p` (rfl).
- `graph_column_parity_energy` :2580 — `4^(n/2)·(1 + n%2) = 2^n` (both parities, one column).
- `omega_small_digit_two` :2596 — 4^5, 4^6, 4^7 own digit 2 by computation.
- `infinite_graph_ternary_two_chokehold` :2611 — under hClosed, every n ≥ 9 shows the two
  in the parity column of the ONE infinite graph.
- **`omega_cut_word_linear`** :2786 — `omegaCutWord s core = omegaCutWord s 1 · core + 3^(s+1)·t`.
- **`omega_observed_digit`** :2827 — for 1 ≤ k ≤ s+1: `digit3 (4^(3^s·core)) (s+k) =
  trit (k−1) of (omegaCutWord s 1 · core)` — ONE object for all tower levels.
- **`omega_tower_level_digit_two`** :2861 — UNIFORM TOWER GATE: all levels k ≥ 3 at once (UNCOND.).
- `omegaShadowTailE` :2892 / `four_power_omega_shadow_wave_tailE` :2924 — observer-form residual input.
- **`omega_row_level_digit_two`** :2961 — UNIFORM ROW LAW: any depth j, sheet zero:
  `2·3^j ≤ omegaCutWord 0 core % 3^(j+1) → digit3 (4^core) (1+j) = 2` (UNCONDITIONAL,
  unbounded in j; `omegaCutWord 0 core = (4^core − 1)/3`, the row word).
- `omegaShadowTailF` :2998 / `four_power_omega_shadow_wave_tailF` :3015 — the second-observer
  residual input (both observer dodges; the terminal input).
- `four_power_omega_shadow_wave_closed` :2325 — alias of the wave (the campaign target name).
- `gst_four_power_creation_certificate_of_omega_cut` :3032 — class-two creation certificate, no hypothesis.
- `omega_binom_mod9_four` :1111 / `_seven` :1124, `omega_mul_mod9_six` :1135 / `_three` :1146,
  `omega_powmul_mod_cubed` :1158 — the binomial-trit toolkit of the second-sheet gates.

### Monolith (ErdosTernary2.lean)

- `noTernaryTwo` :148, `hasTernaryTwo` :195, `has_two_imp_not_no_two` :661,
  `hasTernaryTwo_of_digit` :3414, `no_two_false_digit_witness` :18354 — verdict/digit bridges.
- `c` :255 + `lte_identity` :371 — the LTE tower `4^(3^j) = 1 + 3^(j+1)·c j` (j ≥ 1);
  numerically `lteCoeff s = c s` for s ≥ 1 (receipt R4).
- `erdos_ternary_2_odd_universal` :553 (consumed at :17021) — all odd n ≥ 9, UNCONDITIONAL.
- `erdos_ternary_2_assembled` :2024 (+ its own gap docstring :2019-2020) — the assembled
  case theorem; its documented uncovered set is the dust lane.
- `modular_check_base` :3489 (+ `mod_check_K12` :3019, `mod_check_K16` :3007,
  `hCreationCheck_univ` :4091) — kernel-checked base 5 ≤ K ≤ 500 (bounded `decide` on `powMod`).
- `gstCarry` :4766, `gstDigit` :4769, `gstSpaceAt` :4778, `GSTGraphNode` :4785,
  `GSTForwardEdge` :4818, `GSTGraphWitness` :4822 — the seven-axis graph universe.
- `GSTOmegaState` :6844, `gstOmegaStep` :6857, `gstOmega` :6870,
  `gst_omega_universal_equation` :6890 — the Ω∞ coupled evolution (one theorem, all axes).
- `GSTOmegaInfiniteBadTrace` :7035, `gst_omega_noInfiniteBadTrace_iff_finite_escape` :7179 —
  the infinite-orbit/finite-escape bridge.
- `GSTResidualOmegaTermination` :7058 — DEF with genuine exclusion content, **but its own
  statement carries the child navigation witness as a premise**; the chain that consumed it
  (`gst_omega_termination_s1/s3/stable` :7351/:7382/:7411, `gst_residual_omega_termination`
  :7440) is **QUARANTINED dead code** (:7347-7459), with the retirement note at :7588:
  "(retired unconditional-era crown copy deleted — FV-2R flag 4; the live crown is
  erdos_ternary_2_universal_of_tailF with its input binder)".
- `gst_omega_pressure_no_unbounded_twoS` :11481 — fixed-energy finiteness: a fixed natural
  T has no digit-2 positions above its own size (NOT a forcing law; opposite direction).
- `gst_step6_terminal_packet_kernel` :16758 — certified Step-6 packet (explicitly "does not
  turn the shifted packet into a contradiction").
- `gst_four_power_creation_master_inline` :16894 / `gst_prefix_one_navigation_lift` :16904 —
  POE route, input `hClimb` (= `four_power_happy_climb`, the named seam).
- `GSTPowerTwoWave` :16914, `gst_power_two_wave_large` :16949 — two-wave theorem, input hClimb, a > 500.
- `erdos_ternary_2_even_universal` :16963 — even case, input hClimb.
- `erdos_ternary_2_even_universal_omega` :17003 — even case, input hShadow (the wave).
- `erdos_ternary_2_unconditional_except_shadow` :17017 — odd wing + non-shadow even wing,
  ZERO input (the unconditional core).
- The dispatch chain `four_power_omega_shadow_wave_of_tail/tail2/tail3/tail4/tail5/tailE/tailF`
  :17043/:17076/:17126/:17264/:17470/:17782/:18142 and the closed-wave receipts
  `..._closed_iff_tail3/4/5/E/F` :18096/:18116/:18047/:18068/:18230.
- §7.15 terminal identity block :18377-18527 (cited in §1; the fixed point).
- File header :9 — "0 sorries · 0 errors · the universal theorem carries the observer input;
  §7.15 certifies input ↔ statement". (Repo's own conditionality certificate.)

### Canonical lane files

- GSTCanonicalTailStateIso.lean: `digit3` :9, `carry4` :12, `HappyCell` :15, `Navigation` :18,
  `prefix_slice_quotient_exact` :22, **`prefix_slice_digit_exact`** :31,
  `prefix_slice_carry_seed_zero` :58, `canonical_tail_state_isomorphism` :97,
  `canonical_tail_happy_iff` :107.
- GSTCanonicalCarryDynamics.lean: `carry4_lt_four` :11, `carry4_forward_exact` :18.
- GSTCanonicalEnergyControl.lean: the three exact energy packets :24/:60/:129 — every packet
  retains `4^(3^(s+1)·n) = 1 + 3^(s+2)·T` (the perfect-power energy) plus the child gate,
  BIG-N chord, signed kernel, and the parent seeded bad trace — transport data, no forcing.
- GSTCanonicalBoundaryRigidity.lean: `canonical_block_prefix_exact` :67
  (`4^(3^s) = 1 + 3^(s+1) + 3^(s+2)·(lteCoeff s / 3)`), `canonical_right_residue_exact` :117,
  `canonical_boundary_packet_exact` :223 — at the production cut the boundary packet is
  forced by s alone (rigidity).
- GSTCanonicalFirstGateControl.lean: `gpt56_first_navigation_gate_u_control` :42,
  `gpt56_first_navigation_gate_exact_binary_chord` :94 (NULL chord 2→1→2 after one x2
  column; GST+ chord 2→2→2 after three), `..._short_big1` :199.
- GSTCanonicalFirstGateStandalone.lean: standalone twins :39/:86.
- GST2DMixedEmergence.lean: `outDigit`/`nextCarry` :20/:23, `mixed_cell_emergence` :127
  (8·sevenKernel + 7·U = BIG1 boundary derivative + carry flux + 56·SURVIVE incidence),
  `happy_chord_dichotomy` :145, `mixed_row_emergence` :168, `mixed_rectangle_emergence` :201 —
  the 2D conservation law of the ontology (divergence identity, no forcing).
- GSTCanonicalTailEscapeAudit.lean :3-13 — the axiom audit of the escape chain.

---

## §3 THE DERIVATION (lemma chain)

Notation: `digit3 N p = (N/3^p)%3`, `carry4 N p = (4·(N%3^p))/3^p` (TailStateIso :9/:12).
"trit j of W" := `digit3 W j`. `W_s := omegaCutWord s core`, `M_s := lteCoeff s · core`
(note `omegaCutWord s 1 = lteCoeff s` because `omegaGeoSum s 1 = 1`; and `lteCoeff s = c s`
for s ≥ 1 by :371 vs pow4_three_power_lte_exact — receipt R4).

**L1 (canonical sheet decomposition).** [GREEN, omega_three_free_decomposition :598]
Every K > 0 is K = 3^s·core with 3 ∤ core; s = v₃(K).

**L2 (the Ω-cut factorization).** [GREEN, omega_cut_factor :145]
`4^(3^s·core) = 1 + 3^(s+1)·W_s`, exact, all s, core.

**L3 (full-depth row-tape law).** [NEW, proof]
For all s, core and **all** j ≥ 0:
`digit3 (4^(3^s·core)) (s+1+j) = trit j of W_s`, and `digit3 (4^(3^s·core)) p ∈ {0,1}` for 0 ≤ p ≤ s.
*Proof.* `prefix_slice_digit_exact` (TailStateIso :31) with b = s+1, P = 1 (< 3^(s+1)),
tail = W_s: `digit3 (1 + 3^(s+1)·W_s) ((s+1)+j) = digit3 W_s j`. Rows 0..s: `4^K ≡ 1 (mod 3^(s+1))`
(omega_cut_prefix_one :205) so all those digits are 0 except row 0 = 1. ∎
(The repo uses this slice only inside windows — tower rows s+1..2s+1, sheet row 2s+2,
second-sheet row 2s+3; the all-j form is immediate but unstated. It is the row *tape*:
the entire ternary expansion of 4^K above the cut is the cut word's expansion.)

**L4 (first trit = core mod 3).** [GREEN, omega_cut_digit :187] `trit 0 of W_s = core % 3`.

**L5 (class-two gate).** [GREEN, omega_cut_happy_gate :228 + omega_cut_carry_zero :211]
s ≥ 1, core ≡ 2 (mod 3) → HappyCell (carry 0) at row s+1. Infinite family: all K = 3^s·core, s ≥ 1, core ≡ 2 mod 3.

**L6 (level-two gate).** [GREEN, omega_level2_digit_two :335 + omega_cut_word_mod9-family :240/:276/:290/:306]
s ≥ 1, core ∈ {1,5} (mod 9) (3-free) → digit 2 at row s+2.

**L7 (row-two gate).** [GREEN, omega_row2_digit_two :582] K ≡ 7 (mod 9) → digit 2 at row 2.

**L8 (kernel base).** [GREEN, modular_check_base :3489; hard cases via mod_check_K16 :3007;
bounded-decide receipt hCreationCheck_univ :4091] 5 ≤ K ≤ 500 → hasTernaryTwo (4^K) = true.

**L9 (the coverage split).** [GREEN, omega_digit_two_cases :631]
K ≥ 8 → `omegaShadow K ∨ ∃ p, digit3 (4^K) p = 2`, UNCONDITIONAL.

**L10 (COROLLARY — the unconditional cover).** [NEW, proof = assembly of L4-L9]
Every K ≥ 8 with `¬ omegaShadow K` owns a ternary digit 2 with **zero inputs**; every
8 ≤ K ≤ 500 owns one unconditionally (L8). Coverage map (explicit residue/v₃ conditions on K):

| Family of K = 3^s·core (3 ∤ core) | Law | Row of the 2 |
|---|---|---|
| 8 ≤ K ≤ 500 (any) | kernel base L8 | (computed) |
| core ≡ 2 (mod 3), s ≥ 1 | cut gate L5 | s+1 |
| core ≡ 2 (mod 3), s = 0 | L4 (row 1 = 2) | 1 |
| core ≡ 1,5 (mod 9), s ≥ 1 | level-2 L6 | s+2 |
| core ≡ 7 (mod 9), s = 0 | row-2 L7 | 2 |
| **core ≡ 4 (mod 9), any s** | **SHADOW** | — |
| **s = 0, core ≡ 1 (mod 9)** | **SHADOW** | — |
| **s ≥ 1, core ≡ 7 (mod 9)** | **SHADOW** | — |

*This is the exact boundary of the unconditional ontology: everything outside the three
shadow families is closed.* (Consistency receipt R1: 0 mismatches on [8,20000].)

**L11 (the uniform tower observer — all levels at once).** [GREEN, omega_cut_word_linear :2786 +
omega_observed_digit :2827 + omega_tower_level_digit_two :2861]
For 1 ≤ k ≤ s+1: `digit3 (4^(3^s·core)) (s+k) = trit (k−1) of (omegaCutWord s 1 · core)`;
whenever that trit is 2 (top third of the window mod 3^k), digit 2 at row s+k.
UNBOUNDED in k (every tower level 3,4,5,…,s+1 in one law; levels 3-7 :746/:1047/:1618/:1697/:1971
are its stabilized instances; expcycle rows 3-6 :1393-2171 are its sheet-zero instances).

**L12 (the sheet gates).** [GREEN, omega_sheet_gate_digit_two :953; omega_sheet2_gate_four :1258 /
seven :1307] For core ≡ 1 (mod 3): top trit of `W_s` mod 3^(s+2) → digit 2 at row 2s+2;
second-order binomial trit → digit 2 at row 2s+3 (four-sheet lowest third / seven-sheet middle third).

**L13 (the uniform row observer — all rows at once).** [GREEN, omega_row_level_digit_two :2961]
Sheet zero (K = core 3-free): whenever `2·3^j ≤ W_0 % 3^(j+1)` (trit j of the row word
`W_0 = (4^K − 1)/3` is 2), digit 2 at row 1+j — **for every j, unbounded**.
Together with L3 at s = 0: *the row observer fires exactly at every digit-2 position
≥ 1 of 4^K read through the row word.* The sheet-zero dispatch is therefore: kernel base,
or row observer (any 2 anywhere), or the residual.

**L14 (automatic trits of the shadow).** [NEW, proof]
For shadow cores: trits 0,1 of `M_s = lteCoeff s·core` (s ≥ 1) are (1,0) if core ≡ 4 (mod 9)
and (1,1) if core ≡ 7 (mod 9); trits 0,1 of the row word `W_0` are (1,0)/(1,1)/(1,2) for
K ≡ 1/4/7 (mod 9). *Proof.* `lteCoeff s ≡ 7 (mod 9)` (:240) → `M_s ≡ 7·core (mod 9)`:
7·4 = 28 ≡ 1, 7·7 = 49 ≡ 4 (mod 9). For W_0: `4^K mod 27 = 4^(K mod 9) mod 27` (period 9,
green inside :587 `4^9 % 27 = 1`), so K ≡ 1,4,7 (mod 9) → 4^K ≡ 4,13,22 (mod 27) →
W_0 = (4^K−1)/3 ≡ 1,4,7 (mod 9). ∎ (Receipt R4: 0 failures.)
So in every shadow case the first two rows after the prefix are **never** 2 — the shadow
is exactly where the shallow instruments go blind.

**L15a (the second-sheet correction trit).** [NEW, proof]
For s ≥ 1 and core ≡ 1 (mod 3):
`W_s ≡ M_s + δ·3^(s+2) (mod 3^(s+3))` with **δ = 2 if core ≡ 4 (mod 9), δ = 1 if core ≡ 7 (mod 9)**.
*Proof.* `omega_cut_word_full3` :1178 gives `W_s ≡ M_s + 3^(s+1)·lteCoeff s²·C(core,2) (mod 3^(s+3))`
with C(core,2) = core(core−1)/2. `omega_binom_mod9_four` :1111 / `_seven` :1124:
C(core,2) ≡ 6 / 3 (mod 9). `omega_mul_mod9_six` :1135 / `_three` :1146 (lteCoeff² ≡ 1 mod 3):
lteCoeff²·C(core,2) ≡ 6 / 3 (mod 9). `omega_powmul_mod_cubed` :1158:
`3^(s+1)·X ≡ 3^(s+1)·(X mod 9) (mod 3^(s+3))`, and 3^(s+1)·6 = 2·3^(s+2), 3^(s+1)·3 = 3^(s+2). ∎
(Receipt R4: 132/132 (s,core) pairs, s ≤ 6.)

**L15 (WINDOW CHARACTERIZATION of the s ≥ 1 residual arm).** [NEW, proof]
For s ≥ 1, core ≡ 1 (mod 3), K = 3^s·core, the following are equivalent:
(i) the `omegaShadowTailF` s ≥ 1 dodge conjunction (tower dodge ∀k ∈ [3,s+1]; sheet-gate
dodge; second-sheet dodges — GSTGraphV2OmegaWaveLaw.lean:2998-3010 minus the s = 0 clause);
(ii) `W_s` has no trit 2 in positions 0..s+2;
(iii) **4^K has no digit 2 in rows 0..2s+3** (a finite window of 2s+4 rows).
*Proof.* (ii)⟺(iii): L3 (rows s+1..2s+3 = trits 0..s+2 of W_s; rows 0..s automatic).
(i)⟺(ii): tower dodge reads trits 2..s of `M_s` (L11; `omegaCutWord s 1 = lteCoeff s`);
trits 0,1 of M_s are automatic (L14) and `W_s ≡ M_s (mod 3^(s+1))` (linearity :2786);
sheet-gate dodge is trit s+1 of `W_s` ≠ 2 (`omega_cut_word_mod_pow2` :858: `W_s ≡ M_s (mod 3^(s+2))`);
second-sheet dodges say `M_s`'s trit s+2 ≠ 0 (four-sheet) / ≠ 1 (seven-sheet), which by L15a
(`W_s`'s trit s+2 = (M_s's trit s+2 + δ) mod 3, δ = 2/1) is exactly `W_s`'s trit s+2 ≠ 2. ∎
(Receipt R2: 2165/2165 s ≥ 1 shadow-class members in [501,20000], zero disagreements.)

**L16 (SHEET-ZERO ARM = THE COUNTEREXAMPLE SET).** [NEW, proof]
For 3-free K > 500: the s = 0 arm of `omegaShadowTailF` (K ≡ 1,4 mod 9 + row-observer dodge
∀j ≥ 2) holds **⟺ 4^K is 2-free**.
*Proof.* (⟸) If 4^K is 2-free: K ≢ 2 (mod 3) by L4, K ≢ 7 (mod 9) by L7 → K ≡ 1,4 (mod 9);
every dodge holds because any gate firing would exhibit a digit 2. (⟹) L3 at s = 0 makes
the digit tape of 4^K = {row 0 = 1} ∪ trits of W_0; the dodge kills trits ≥ 2 of W_0 and
L14 kills trits 0,1; hence W_0 is 2-free, hence 4^K is 2-free. ∎
**So on sheet zero the ontology is maximal: the only uncovered object is the 2-free power
itself. The residual IS the counterexample set — the fixed point is tight on this arm.**

**L17 (2-free ⟹ shadow membership).** [NEW, proof]
If 4^K is 2-free and K ≥ 8 then K satisfies `omegaShadowTailF` (whichever sheet it sits on).
*Proof.* L4/L6/L7 force the shadow class (core ≡ 1 mod 3; s ≥ 1 → core ≡ 4,7 mod 9;
s = 0 → core ≡ 1,4 mod 9). All dodge conditions are monotone consequences of "no digit 2
anywhere" via L15/L16 (each dodge is the negation of a gate that would exhibit a 2). ∎

**L18 (the dispatch chain and the terminal identity).** [GREEN]
`four_power_omega_shadow_wave_of_tail … _of_tailF` :17043-:18238 (each tail input discharges
the full wave through the kernel base + the gate families + both observers);
`four_power_omega_shadow_wave_closed_iff_tailF` :18230;
`erdos_even_conjecture_iff_tailF` :18425 — **the second-observer input and the even-half
conjecture are one object, kernel-certified in both directions.**

**L19 (THE ASSEMBLY THEOREM).** [NEW, proof]
`(∀ K ≥ 8, noTernaryTwo (4^K) = false)` ⟺ **[GAP-A1] ∧ [GAP-A2]**, where

- **GAP-A1 (deep-wave law, s ≥ 1 arm):** for every s ≥ 1, core ≡ 4,7 (mod 9), 3 ∤ core,
  3^s·core > 500 **with `W_s` 2-free in trits 0..s+2** (the window dodge of L15):
  `∃ n ≥ s+3, trit n of W_s = 2` — i.e. every window-dodger fires above its window.
- **GAP-A2 (sheet-zero dust emptiness):** for every 3-free K ≡ 1,4 (mod 9) with K > 500:
  the row word `(4^K − 1)/3` contains a trit 2 (equivalently by L16: no 2-free 4^K with
  3-free exponent above the kernel base).

*Proof.* (⟸) Take a shadow K > 500 (K ≤ 500 is L8). If s = 0: by L16 the tailF witness
conditions say 4^K is 2-free, contradicting GAP-A2 — so no sheet-zero witness exists.
If s ≥ 1: by L15 the witness is a window-dodger, and GAP-A1 supplies trit n = 2 of W_s at
some n ≥ s+3, i.e. by L3 a digit 2 of 4^K at row s+1+n ≥ 2s+4. Feed the two cases as the
`hTailF` input of `four_power_omega_shadow_wave_of_tailF` :18142 → the wave →
`erdos_ternary_2_universal_of_tailF` :18344. (⟹) If the conjecture holds, every shadow
exponent > 500 owns a 2; for s = 0 members L16 turns this into GAP-A2; for s ≥ 1 members
either the window has a 2 (then it is not a tailF witness) or the 2 lies above the window,
which is GAP-A1. ∎

**Consequence (boundary of the ontology).** By L18 the conjunction GAP-A1 ∧ GAP-A2 is
*equivalent* to the terminal input `four_power_omega_shadow_wave_tailF`; by L16 GAP-A2 is
the conjecture verbatim on 3-free exponents; by L15 GAP-A1 is the tail input verbatim on
window-dodgers. **No reassembly of the ontology's existing gate families can close either
gap:** the dust tree is immortal at every finite level (2^(L−1) surviving classes mod 3^L —
receipt R3, L ≤ 10; green pins 2-4-8-16-32 through mod 729 per the construction), so GAP-A2
has no finite residue-class solution, and GAP-A1's witnesses fire up to 22 rows beyond
their windows already on [501,20000] (receipt R2), so no window extension bounded by any
fixed function of s that the current instruments reach will close GAP-A1.

### The boss's stance, verified or refuted (file:line chain)

**Weak form — VERIFIED.** The infinite/unbounded machinery exists and is green:
`omega_tower_level_digit_two` :2861 collapses **every** tower level into one law;
`omega_row_level_digit_two` :2961 collapses **every** sheet-zero row into one law;
`gst_omega_universal_equation` :6890 evolves all coupled axes in one theorem;
`GSTOmegaInfiniteBadTrace` :7035 + finite-escape :7179 give the genuine n→∞ orbit object;
`infinite_graph_ternary_two_chokehold` :2611 reads both parities through the ONE infinite
graph column (`graph_column_parity_energy` :2580). All unconditional as stated.

**Strong form ("the forcing is already shown, the dust lane is covered") — REFUTED, by the
repo's own certificates:**
1. Every terminal statement consumes a named input: `erdos_ternary_2_universal_of_tailF (hTailF)` :18344;
   `erdos_ternary_2_even_universal (hClimb)` :16963; `erdos_ternary_2_even_universal_omega (hShadow)` :17003;
   `infinite_controller_ternary_two_chokehold (hTailF)` :18466.
2. The one era that claimed unconditional closure — the "certified residual omega termination
   chain" (`gst_residual_omega_termination` :7440) — is **quarantined dead code** (:7347-7459),
   self-labeled "Legacy residual overproof … proof archaeology only" (:7341-7345), with the
   crown retirement note at :7588; and even its own definition :7058 carries the child
   navigation witness as a premise (it never was input-free).
3. The fixed point `erdos_even_conjecture_iff_tailF` :18425: the terminal input IS the
   conjecture. The file header :9 states it: "the universal theorem carries the observer input".
4. Where the cover breaks, concretely: **K = 522 = 3²·58** (four-sheet, core 58 ≡ 4 mod 9).
   Its window is rows 0..2s+3 = 0..7; every ontology instrument (tower observer k ≤ s+1 = 3,
   sheet gate row 6, second-sheet gate row 7) stops at row 7; the first digit 2 of 4^522
   lands at **row 12** (receipt R2). 821 such window-dodgers exist in [501,20000] alone.

---

## §4 GAP AUDIT

What this derivation proves: the **exact unconditional cover** (L10): every K ≥ 8 outside
the three Ω-shadow families owns digit 2 with zero inputs; the shadow's sheet-zero arm is
exactly the 2-free counterexample set (L16); the shadow's s ≥ 1 arm is exactly the
window-dodger set "no 2 in rows 0..2s+3" (L15); the assembly reduces the whole conjecture
to GAP-A1 ∧ GAP-A2 (L19), and this reduction is certified equivalent to the repo's own
terminal identity (L18).

What remains — two NAMED GAPS (each is a NEW LEMMA with statement + obstruction):

**GAP-A1 (deep wave above the window, sheets s ≥ 1).**
Statement: ∀ s ≥ 1, ∀ core ≡ 4,7 (mod 9), 3 ∤ core, 3^s·core > 500, if `omegaCutWord s core`
is 2-free in trits 0..s+2 then ∃ n ≥ s+3 with trit n of `omegaCutWord s core` = 2.
Obstruction: the ontology's deep instruments stop at second binomial order
(`omega_cut_word_full3` :1178 reaches mod 3^(s+3) only); the tower observer is bounded by
k ≤ s+1 **by construction** (the window in which `W_s ≡ lteCoeff s·core`, linearity :2786);
no green law reads trits of `W_s` at positions ≥ s+3. Reading them requires the full
binomial expansion of the geometric sum `Σ_{j<core} (4^(3^s))^j` — the general level-n
wave (Lane C) — or an exponent-descent contradiction (Lane B). Machine facts that shape
any attempt (receipt R2, bounded [501,20000]): all 821 window-dodgers fire, first-2 rows
6..27, depth beyond window up to 22; the window-dodge is **not hereditary** under
K → K/3 (descent breaks on 114 of 181 testable members), so no naive sheet-induction closes it.

**GAP-A2 (sheet-zero dust emptiness).**
Statement: ∀ 3-free K ≡ 1,4 (mod 9), K > 500: `(4^K − 1)/3` has a trit 2.
Obstruction: by L16 this is exactly "no 2-free 4^K with 3-free exponent above the kernel
base" — the Lagarias 3-adic Cantor-lane core. The dust tree never empties at any finite
level (2^(L−1) classes mod 3^L, R3; `dust_immortal` is green in GSTTailFInfiniteRead),
so no finite gate family can do it; the obstruction is the passage from "every finite
level has survivors" to "no natural number survives all levels" — the 3-adic limit
argument (Lane B's mission: high trits of a fixed natural vanish, so infinite survival
forces the row word of K itself to be 2-free, and the contradiction must come from the
Cantor/arithmetic structure of `(4^K−1)/3`, e.g. Senge–Straus-type inputs or the
self_read/noise machinery of the construction).

Secondary (informational, not blocking): the quarantined block :7347-7459 shows a prior
"unconditional" claim existed and was retired — any Lane A revival must not re-consume
`GSTResidualOmegaTermination` (:7058) without discharging its child-witness premise.

---

## §5 LEAN INTEGRATION SKETCH (for the orchestrator; no .lean files were touched)

1. **L3 (full-depth row tape)** — one-line addition in `GSTGraphV2OmegaWaveLaw.lean` next to
   `digit3_window` (:901): `theorem omega_cut_tape (s core j : Nat) : digit3 (4^(3^s*core)) (s+1+j) = digit3 (omegaCutWord s core) j := by have h1 : (1:Nat) < 3^(s+1) := ...; simpa [omega_cut_factor s core] using prefix_slice_digit_exact (s+1) 1 _ j h1`
   (mirrors the existing uses at :326/:735/:940/:1036/:1246/:1607/:1686/:1960).
2. **L15a (correction trit)** — a named `have`-level lemma beside `omega_cut_word_full3`
   (:1178), assembling :1111/:1124/:1135/:1146/:1158 exactly as `omega_sheet2_gate_four`
   :1258 does internally; statement `omegaCutWord s core % 3^(s+3) = (lteCoeff s * core + δ*3^(s+2)) % 3^(s+3)`.
3. **L15 (window characterization)** — new theorem in the same file, consuming L3+L15a+
   :858+:2786; then **L16/L17** as two more theorems (L16 needs only L3+L14+the row-word
   identification `omegaCutWord 0 core = (4^core-1)/3`, available from `omega_cut_factor 0 core`
   as in :2966-2971).
4. **L19 (assembly)** — in the monolith's §7.15 region (after :18238): two defs
   `four_power_deep_wave_above_window` / `four_power_sheet_zero_dust_empty` and one
   `theorem erdos_even_conjecture_iff_deep_wave_and_dust` following the exact shape of
   `erdos_even_conjecture_iff_tailF` :18425 (constructor pairs: .mp via L17+arm split,
   .mpr via `four_power_omega_shadow_wave_of_tailF` :18142). This adds no new mathematical
   content beyond L15/L16/L17 but makes the two gaps the repo's named objects.
5. Downstream: GAP-A1 is Lane C's general level-n wave target; GAP-A2 is Lane B's descent
   target. The dispatch glue for both already exists (:18142, :18425).

---

## §6 VERIFICATION RECEIPTS (all runs executed this session; python3; exact bounds)

**R1 — coverage map verification.**
Command: python3, K ∈ [8, 20000]; classify by L4-L9; verify predicted digit = 2 by
`digit_row(K,row) = (pow(4,K,3^(row+1)) % 3^(row+1)) // 3^row`.
Output (verbatim):
```
shadow members in [8,20000]: 6498
first 20 shadow: [(505, 0, 505), (507, 1, 169), (508, 0, 508), (514, 0, 514), (517, 0, 517), (522, 2, 58), ...]
mismatches (predicted digit != 2): 0
unclassified: 0 []
shadow members in [8,20000] with NO digit-2 in rows 0..60: []
```
Bound: 12,000 exponents × ≤ 61 modular reads. Every non-shadow K in [8,20000] has its
digit 2 at exactly the law-predicted row (0 mismatches); every K in [8,20000] fires
within row 60; the s = 0 tailF arm (2-free powers) is EMPTY on this range.

**R2 — window characterization + residual depth.**
Command: python3, K ∈ [501, 20000], s ≥ 1 shadow class; `tailF_s1_dodge(s,core)`
implemented verbatim from GSTGraphV2OmegaWaveLaw.lean:2998-3010 (with
`omegaCutWord s core = lteCoeff s · ((4^(3^s))^core − 1)/(4^(3^s) − 1)`,
`lteCoeff s = (4^(3^s)−1)/3^(s+1)`) vs `window_2free(K,s)` (no digit 2 in rows 0..2s+3).
Output (verbatim):
```
s>=1 shadow class members in [501,20000]: agree(window==dodge): 2165 disagree: 0 [] max s seen: 7
s>=1 residual members in [501,20000]: 821
  first-2 row: min 6 max 27 | beyond-window max: 22
  sample: [(522, 2, 58, 12, 7), (561, 1, 187, 7, 5), (567, 4, 7, 21, 11), (579, 1, 193, 6, 5), ...]
sheet-zero residual members in [501,20000] (first-2 at row>=3 or none): 4333
  their first-2 rows: min 3 max 21
descent-closed (parent also window-2free): 67 | descent-broken: 114
  [(522, 2, 58, 174, 1), (567, 4, 7, 189, 3), (792, 2, 88, 264, 1), ...]
distinct cores in s>=1 residual: 751
their 4^core first-2 rows: min 2 max 19 | cores with 4^core 2-free in rows 0..3: 340
```
Bound: ≤ 19,500 exponents × ≤ 120 modular reads + 132 cut-word big-int constructions
(K ≤ 3^7·79, cut words ≤ ~10^90). The 4,333 sheet-zero entries are first-2-at-row-≥-3
members (all killed by the unbounded row observer L13); the true s = 0 arm (2-free) is empty.

**R3 — dust immortality counts.**
Command: python3, count 3-free c mod 3^L with 4^c having no digit 2 in rows 1..L.
Output (verbatim):
```
L=2: dust classes mod 3^2 = 2 (expected 2^1 = 2)
L=3: 4 (exp 4)   L=4: 8 (exp 8)   L=5: 16 (exp 16)   L=6: 32 (exp 32)
L=7: 64   L=8: 128   L=9: 256   L=10: 512  (all = 2^(L-1))
```
Bound: Σ 3^L·L ≈ 6·10^6 ops for L ≤ 10. Matches the green dust pins (2-4-8-16-32 through
mod 729) and extends them to mod 3^10 — the dust tree never empties at any tested level.

**R4 — lemma numerics (L14, L15a, lteCoeff = c).**
Command: python3, s ∈ [1,6], cores 4+9t / 7+9t (t ≤ 11), 3-free; and lteCoeff(s) = c(s), s ≤ 5.
Output (verbatim):
```
lteCoeff==c: True
second-sheet correction verified on 132 (s,core) pairs, failures: 0
sheet-gate congruence W==M mod 3^(s+2) verified on 203 pairs, failures: 0
auto-trit failures: 0
```
Bound: ≈ 335 big-int constructions (cut words up to ~10^90).

Cross-session data cited with label (NOT re-run here, per lane split): the exhaustive
below-16,777,216 fire scan, max fire row 42, and the deep-hider laws (3^777 → row 779)
are the brief §3 machine receipts (Lane D owns ANY_NUMBER_TILL_INFINITY_RECEIPTS.md).

---

## §7 SELF-AUDIT (mistakes caught in-session; ledger-worthy items flagged)

1. **Mislabel caught before delivery:** R2's first draft called the 4,333 sheet-zero
   entries "residual members"; they are first-2-at-row-≥3 members (row-observer kills).
   The true s = 0 arm is the 2-free set, empty on the scan. Corrected in §6 wording.
2. **Grep noise:** the initial keyword sweep for "omega/4D/emergent/worldtrace" matched
   the tactic `omega` (300+ false hits); re-scoped with word boundaries. "worldtrace" and
   "emergent" have ZERO occurrences in the monolith itself — the worldtrace law lives at
   GSTGraphV2OmegaWaveLaw.lean:119 and the emergence laws in GST2DMixedEmergence.lean; the
   "4D" hits (:7848, :9177) are variable names (`4*c0 < D*c0`), not a 4D section.
3. **Quarantine discovery:** the commit-message phrase "Activate certified residual omega
   termination chain" (header :24) initially read as live; direct read showed the whole
   chain commented out (:7347-7459) with the retirement note (:7588). Ledger-worthy for
   the orchestrator: **commit messages must not be read as code state** (variant of
   ledger 068 snapshot-reasoning).
4. **Docstring under-report:** the monolith's own `erdos_ternary_2_assembled` docstring
   (:2019-2020) names the uncovered set as "b mod 9 ∈ {4,7}, s ≥ 1" but omits the
   sheet-zero families (core ≡ 1,4 mod 9 at s = 0) that `omegaShadow` :617 correctly
   includes — the precise gap is the shadow def, not the docstring.
5. No .lean file was touched, no git command was run, no push. All numbers in §6 come from
   the four quoted runs; all file:line citations come from this session's Reads.
