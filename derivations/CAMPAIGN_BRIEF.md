# CAMPAIGN BRIEF — THE ONE PROP
# Erdős Ternary Campaign · Branch sol/kyo-gate-universe-wire · Clone /home/z/erdosternary2

## 0. PROTOCOL — MANDATORY ORDER (no exceptions)

1. Read `/home/z/my-project/download/boss_upload_V5_SKILL.md` IN FULL (389 lines) — your operating protocol.
2. Read `/home/user_skills/maths-researcher/MISTAKE_LEDGER.md` IN FULL — 69 permanent bans. Rehearse them.
3. Read the LAST 3 SECTIONS of `/home/z/my-project/worklog.md` — what has been done.
4. Read THIS brief in full.
5. Read YOUR lane's files (targeted lists in §7; every citation you make must come from YOUR OWN Read this session — never from summaries).
6. Write your derivation file.
7. Append your worklog entry (template in §6).

## 1. THE TARGET — ONE Prop, six green-equivalent forms

All six are INTER-DERIVABLE through GREEN (machine-verified, CI-certified) bridges.
Proving ANY ONE proves ALL. Pick your lane's form and attack.

- `four_power_happy_climb : ∀ K ≥ 8, ∃ p ≥ 3, HappyCell (carry4 (4^K) p) (digit3 (4^K) p)` — GSTInfiniteFourPowerNavigation.lean:141 (a def, the named seam)
- `the_act : ∀ K : Nat, 8 ≤ K → noTernaryTwo (4^K) = false` — GSTTheAct.lean
- tree-escape: `∀ K ≥ 8, ∃ j, (digit3 (4^(K % 3^j)) (j+1) + digit3 K j) % 3 = 2` — hypothesis of hTailF_of_feedback, GSTTheActConstruction.lean:489-491
- no-Cantorian: `¬ ∃ K ≥ 8, CantorianPower K` — input of hTailF_of_no_cantorian, GSTClimbInfiniteFamily.lean:460
- dust-empty: `∀ K ≥ 8, ¬ WindowCleanDust K` — input of hTailF_of_dust_empty, GSTDiagonalRead.lean:396
- `GSTGraphV2OmegaWaveLaw.four_power_omega_shadow_wave_tailF` — the statement hTailF delivers (GSTTailFProof.lean:216, ONE named input hClimb)

PLAIN LANGUAGE: prove that the only powers of 4 with NO ternary digit 2 are
4^0 = 1, 4^1 = 4, 4^4 = 256. (The odd half of Erdős ternary is green:
erdos_ternary_2_conjecture_odd. This is the even half.)

## 2. WHAT IS GREEN (the bridge map)

- Main.lean: `the_monolith_wire` (line 34) + `the_construction_wire` (line 55) — both CI-green.
- GSTTheActConstruction.lean — 30 theorems, 0 sorries: `self_read` (:79), the uniform kill engine `feedback_fire_of_class` (:196), cascade levels four and five (16 dead classes mod 243 fire row 5; 16 classes mod 729 fire row 6), dust pins 2-4-8-16-32 (mod 9/27/81/243/729), `noise_window_law` (:346), `unique_dead_child` (:355).
- GSTGraphV2OmegaWaveLaw.lean: `omega_wave_climb_class_two` (~:489) — every K = 3^a·core, a ≥ 2, core ≡ 2 mod 3 satisfies the FULL climb statement, UNCONDITIONAL. `omega_wave_digit_two_class_level_two` (~:506) — core ∈ {1,5,6} mod 9 → digit two at row a+2, UNCONDITIONAL.
- GSTTailFOneLane.lean: `one_lane_complete` — every exponent: digit two OR full dust certificate, no hypothesis.
- GSTTailFInfiniteRead.lean: `the_infinite_read` — dust immortal + blade 1-of-3 + survivors spawn + non-dust towers die + terminal identity.
- GSTClimbTruthValue.lean: the conditionality certificate — the single hypothesis carries the entire remaining content.
- GSTClimbInfiniteFamily.lean: `tower_dust_empty` (no 3-free core has a never-firing multiplicative-three tower), `the_act_iff_no_cantorian`, `hTailF_of_no_cantorian` (:460).

## 3. VERIFIED FACTS you may use (with provenance)

- `self_read` (GREEN, construction:79): digit3 (4^K) (j+1) = (digit3 (4^(K % 3^j)) (j+1) + digit3 K j) % 3 — every row of every power reads the exponent through the prefix-power's stream.
- LTE: v₃(4^m − 1) = 1 + v₃(m) (hunt it in GSTCanonicalTailLTE.lean — verify where green).
- The cube law: 4^(3^(ℓ+1)) = (4^(3^ℓ))³ and (1+u)³ = 1 + 3u + 3u² + u³ with u = 3^ℓ·c_ℓ gives c_{ℓ+1} ≡ c_ℓ (mod 3); c₀ = 1 → **c_ℓ ≡ 1 mod 3 for ALL ℓ** (c₀=1, c₁=7, c₂=9709 — verified numerically; the induction is 3 lines — YOU make it airtight).
- Derivation of self_read from the tower: 4^K = 4^r·(4^(3^ℓ))^s = 4^r·(1+3^(ℓ+1)c_ℓ)^s ≡ 4^r·(1 + 3^(ℓ+1)·c_ℓ·s) mod 3^(ℓ+2); since 4^r ≡ 1 mod 3 and c_ℓ ≡ 1 mod 3: digit_{ℓ+1}(4^K) = (digit_{ℓ+1}(4^r) + s) mod 3, s = K div 3^ℓ, s mod 3 = trit_ℓ(K).
- Dust tree: root trit₀ = 1 (K ≡ 1 mod 3); at level j+1, parent r = K mod 3^j, the ONE dead child-trit = (2 − digit_{j+1}(4^r)) mod 3; the other two children survive; dust classes mod 3^ℓ = 2^(ℓ−1) exactly (machine-verified through level 13; green through level 6).
- MACHINE RECEIPTS (ANY_NUMBER_TILL_INFINITY_RECEIPTS.md — read it): full period 1,594,323 enumerated; EXHAUSTIVE below 16,777,216 — every K in [8, 16777216) fires, ONLY {0,1,4} escape; max fire row 42; 20,000 random up to 10⁹ all fire; 137 monsters up to 19,729 digits all fire; DEEP HIDERS: 3^777 fires row 779, 3^3333 row 3335, 3^5000 row 5002 (the n+2 law); 3^n+1 fires at row n+4; self_read 280/280 at 10^1000.
- The infinite-path picture: a natural Cantorian K has all high trits 0, so survival at every deep level requires noise = digit_{ℓ+1}(4^(K mod 3^ℓ)) = 2 forever; but K mod 3^ℓ → K 3-adically, so this forces digit 2s in 4^K itself — TOWARD contradiction with Cantorian. The machine data says every path ≥ 8 dies within 42 rows. THE ARGUMENT MUST BE MADE UNIFORM.

## 4. THE UNCOVERED OBJECT (precise)

3-free K ≡ 1 mod 3, K ≥ 8, on the dust path at every level ⟺ 4^K is ternary-2-free.
The 32 dust residues mod 729 are pinned (green). The omega wave covers every
3-divisible exponent (a ≥ 1: class-two + level-two families) UNCONDITIONALLY.
What remains: the 3-FREE dust cores — prove none ≥ 8 survives, i.e. the only
2-free powers of 4 are 1, 4, 256.

## 5. THE TEN BANS — what NOT to think

1. NO "this is open/hard/impossible/needs deep number theory" — BANNED. If stuck: reframe silently (7 ways), then output the next attempt.
2. NO prose-only deliverables: the derivation must be a CHAIN of precise lemma→lemma statements, each (i) cited green theorem with file:line from YOUR OWN read, (ii) NEW lemma with full proof, or (iii) explicitly flagged NAMED GAP with the exact obstruction. A derivation ending in a named honest gap IS a deliverable. A derivation PRETENDING completeness with a hidden hole is FABRICATION — firing offense.
3. NO trusting summaries/snapshots — every citation verified by your own Read THIS session (ledger 068).
4. NO editing .lean files, NO git commands, NO push, NO touching the monolith. Markdown derivation ONLY. The orchestrator does Lean integration after review.
5. NO heavy compute: python3 OK, bounded (< 10^7 operations, < 120s per run). No OOM (skill §20). tools_any_number_infinity.py stages period/sparse run in seconds if you need fresh data.
6. NO hedging words ("honestly", "I believe", "it seems") — state facts. If unsure, VERIFY (run/grep/read), then state.
7. NO stopping before the deliverable file is written AND the worklog entry appended.
8. Do NOT re-litigate the target: the iff bridges are GREEN. Attacking any of the six forms attacks all.
9. Do NOT fabricate numerics: every number you state comes from a run YOU executed this session, command quoted — or is labeled UNVERIFIED.
10. Do NOT write final Lean proofs — mathematical derivation first. DO include §5 Lean integration sketch.

## 6. DELIVERABLE FORMAT (mandatory)

File: `/home/z/erdosternary2/derivations/DERIVATION_<LANE>.md` (lane ∈ {A_ONTOLOGY, B_DESCENT, C_OMEGA, D_WORLDTRACE})

- §1 THE TARGET — the exact statement your lane attacks (verbatim).
- §2 GREEN INVENTORY — every law you use, file:line, one-line statement each.
- §3 THE DERIVATION — full mathematical detail, lemma → lemma, every step justified. Number every lemma (L1, L2, ...). Mark each: [GREEN, cite] / [NEW, proof] / [GAP, obstruction].
- §4 GAP AUDIT — what your derivation proves vs what remains; each remainder as a NAMED NEW LEMMA with exact statement and the obstruction to its proof.
- §5 LEAN INTEGRATION SKETCH — where/how the derivation would land (GSTTheActConstruction.lean extension or new module; which existing green theorems it calls).
- §6 VERIFICATION RECEIPTS — any numerics you ran, commands + outputs verbatim, exact bounds.
- §7 SELF-AUDIT — any mistake you caught yourself making (ledger-worthy items noted for the orchestrator).

WORKLOG APPEND (mandatory, at the very end):
```
---
Task ID: 9-<x>
Agent: opus-<lane>
Task: <one line>

Work Log:
- <steps>

Stage Summary:
- <key results: lemmas proven, gaps named, files produced>
```
Append to `/home/z/my-project/worklog.md` (do NOT overwrite; append at end).

REPORT BACK to orchestrator (your final message): ≤ 400 words — what was derived, what's green-citable, what gaps remain named, your derivation file path.

## 7. LANE ASSIGNMENTS (union = monolith + all imports)

### LANE A — A_ONTOLOGY (the monolith's own universe)
Files: ErdosTernary2.lean (STRUCTURE SWEEP first: grep namespace/theorem maps, then read the GST v2 graph / omega wave / 4D emergent law / worldtrace sections in targeted chunks — 18,527 lines, chunked), GSTGraphV2OmegaWaveLaw.lean (FULL), GSTCanonicalTailStateIso.lean, GSTCanonicalCarryDynamics.lean, GSTCanonicalEnergyControl.lean, GSTCanonicalBoundaryRigidity.lean, GSTCanonicalFirstGateControl.lean, GSTCanonicalFirstGateStandalone.lean, GST2DMixedEmergence.lean, GSTCanonicalTailEscapeAudit.lean.
Mission: extract EVERY unconditional digit-2-forcing law in the monolith's ontology (GST v2 graph, omega wave, 4D emergent laws, first gates, energy control). Map which exponent families each covers. Then: assemble the cover of ALL K ≥ 8 from what exists; if the cover is incomplete, derive the exact additional law that completes it. The boss's stance: the forcing IS in the Lean, through INFINITE/UNBOUNDED machinery — hunt it (unbounded quantifiers, infinite family theorems, the tower observers §7.13-7.14 of the omega law file).

### LANE B — B_DESCENT (the feedback-tree contradiction)
Files: GSTTheActConstruction.lean (FULL), GSTClimbInfiniteFamily.lean (FULL), GSTDiagonalRead.lean (FULL), GSTCanonicalTailLTE.lean, GSTCanonicalSevenAxisBridge.lean, GSTTailFOneLane.lean, GSTTailFInfiniteRead.lean, GSTClimbTruthValue.lean, GSTTheAct.lean, Main.lean.
Mission: assume a Cantorian K ≥ 8 (4^K 2-free forever) and DERIVE A CONTRADICTION. Weapons: self_read + LTE + noise_window_law + unique_dead_child + the dust pins + tower_dust_empty + the 3-adic limit argument (high trits vanish → noise must be 2 forever → 3-adic convergence forces digit 2s in 4^K itself). Target: the only infinite paths are {0, 1, 4}.

### LANE C — C_OMEGA (extend the wave to the dust cores)
Files: GSTGraphV2OmegaWaveLaw.lean (FULL, careful), GSTInfiniteFourPowerNavigation.lean (FULL), GSTFourPowerHappyProvider.lean (FULL), GSTFourPowerDirectExistence.lean, GSTFourPowerDirectExistenceFromHappy.lean, GSTFourPowerDirectNo22.lean, GSTFourPowerDirectResidue.lean, GSTFourPowerDirectResidue27.lean, GSTFourPowerDirectResidue81.lean, GSTFourPowerExponentTritObstruction.lean, GSTFourPowerDirectFailedRelocationState.lean, FOUR_POWER_DIRECT_EXISTENCE_RESET.md, GSTTailFProof.lean (FULL).
Mission: the omega wave covers core ≡ 2 mod 3 (climb at cut a+1) and core ∈ {1,5,6} mod 9 (digit two at a+2) UNCONDITIONALLY. Derive the GENERAL level-n wave law: for K = 3^a·core, digit_(a+n) of 4^K as a function of core mod 3^n — and show which residue classes it kills. Then push: which dust cores (≡ 1 mod 3, 3-free, the 32 residues mod 729) fall to wave levels n = 3, 4, 5, ... — and whether the wave + descent on a covers everything ≥ 8.

### LANE D — D_WORLDTRACE (binomial/carries/empirics → proof strategy)
Files: ANY_NUMBER_TILL_INFINITY_RECEIPTS.md, tools_any_number_infinity.py, monolith worldtrace sections (grep "worldtrace" in ErdosTernary2.lean, chunked reads), GSTCanonicalCarryDynamics.lean, CarryWordScratch.lean, BadLanguageMagnitudeScratch.lean, CanonicalPrefixScratch.lean, CanonicalOriginModulusScratch.lean, CanonicalOriginCutIntersectionScratch.lean, GSTExponentLiftScratch.lean, GSTFinalPrefixOneDirectU2DCollision.lean, GSTFinalPrefixOneStep6Boundary.lean, GSTFinalPrefixOneStep6Infinite.lean, GSTFinalPurePowerResidueTransplant.lean, GSTFinalResidualBinaryBoundaryBridge.lean.
Mission: the binomial structure 4^K = (1+3)^K = Σ C(K,i)3^i; Lucas mod 3 (C(K,i) ≢ 0 mod 3 iff i tritwise ⊆ K); the carry propagation = the "noise"; the c_ℓ ≡ 1 tower law (prove the 3-line induction airtight); the 3-adic logarithm viewpoint; turn the machine's empirical laws (n+2 for 3^n, n+4 for 3^n+1, doubling dust, max-row-42 exhaustives) into LEMMAS with proof strategies. The scratch files are the dead chat's failure maps — extract what failed and why, so your derivation does not repeat it. Any heuristic (equidistribution etc.) MUST be flagged UNPROVEN — no conjecture may present as fact.

## 8. ENVIRONMENT RULES

- Repo: /home/z/erdosternary2 (clone, branch sol/kyo-gate-universe-wire). The .lake/ dir holds 17k+ build files — NEVER grep the repo root without a *.lean glob filter (timeouts).
- Monolith ErdosTernary2.lean = 18,527 lines: grep for sections first (namespaces, theorem names), then Read with offset/limit.
- python3 available. NO bun, NO npm, NO servers, NO touching /home/z/my-project's Next.js app.
- Do NOT modify the mistake ledger (orchestrator's duty); note ledger-worthy items in your §7.
- You have NO git write access rights usage — do not attempt.
