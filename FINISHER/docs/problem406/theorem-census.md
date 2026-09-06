# Problem 406 theorem census

Source branch: `sol/problem406-professionalization-green-20260906`.

Census workflow head when measured: `ab9a8d2faa8fedddcc34252a5fa53ca5f786fe1f`.

Census job: `theorem-census`, run `34041156515`, job `101508041583`.

The census was produced by `scripts/problem406_repo_census.py`. The script is read-only and scans the checked-out repository. It counts custom Lean source files, computes the recursive custom import closure of `ErdosTernary2.lean` excluding external Lean libraries such as Mathlib, and classifies theorem/lemma declarations by deterministic lexical/path rules.

## Direct imports of the main monolith

`ErdosTernary2.lean` directly imports these custom modules:

1. `GSTTactic`
2. `GSTPrefixOneU2DCollisionProof`
3. `GSTPrefixOneOntologicalEscape`
4. `GSTGraphV2ProductionLaws`
5. `GSTGraphV2InfiniteControllerBridge`
6. `GSTGraphV2PerfectPowerBlockProbe`
7. `GSTU2DSharpCrossingBlock`
8. `GSTFinalPurePowerResidueTransplant`

It also directly imports external Mathlib modules:

1. `Mathlib`
2. `Mathlib.Tactic.Linarith`
3. `Mathlib.Tactic.Ring`

## Line counts

| Scope | Files | Lines |
| --- | ---: | ---: |
| Main monolith only, `ErdosTernary2.lean` | 1 | 17,041 |
| Main monolith + recursive custom import closure | 74 | 30,416 |
| Main monolith + recursive custom import closure + all tactic files | 76 | 30,859 |
| All custom Lean source files in repo, including snapshots/workbench/archive files | 976 | 156,991 |

## Declaration counts

### Main monolith + recursive custom import closure

| Declaration kind | Count |
| --- | ---: |
| theorem | 1,395 |
| lemma | 1 |
| def | 361 |
| structure | 25 |
| inductive | 7 |
| abbrev | 1 |
| axiom | 1 |
| Total declarations | 1,791 |
| Total theorem-like declarations, theorem + lemma | 1,396 |

### Main monolith + recursive custom import closure + all tactic files

| Declaration kind | Count |
| --- | ---: |
| theorem | 1,395 |
| lemma | 1 |
| def | 361 |
| structure | 25 |
| inductive | 7 |
| abbrev | 1 |
| axiom | 1 |
| Total declarations | 1,791 |
| Total theorem-like declarations, theorem + lemma | 1,396 |

### All custom Lean source files in repo

| Declaration kind | Count |
| --- | ---: |
| theorem | 1,992 |
| lemma | 1 |
| def | 499 |
| structure | 40 |
| inductive | 12 |
| abbrev | 12 |
| axiom | 1 |
| Total declarations | 2,557 |
| Total theorem-like declarations, theorem + lemma | 1,993 |

## Theorem-family classification for the live monolith closure

These counts use the live scope requested for architecture work: `ErdosTernary2.lean` plus recursive custom imports plus all tactic files.

| Family | Theorem-like count |
| --- | ---: |
| Final Problem406 theorem layer | 795 |
| Canonical tail / collision / wave engine | 194 |
| Four-power / common-two arithmetic engine | 193 |
| Exponent-prefix / trit obstruction engine | 62 |
| Carry / affine information-state engine | 27 |
| Ternary digit arithmetic engine | 17 |
| Certificate / provider / bridge layer | 16 |
| Custom tactic / automation layer | 11 |
| General Space Theory proper | 81 |
| Total theorem-like declarations | 1,396 |

Therefore, theorem-like declarations outside General Space Theory proper in the live monolith/import/tactic scope:

```text
1,396 total theorem-like declarations - 81 General Space Theory proper = 1,315 non-GST theorem-like declarations
```

## Non-GST theorem families in the live scope

| Non-GST family | Theorem-like count |
| --- | ---: |
| Final Problem406 theorem layer | 795 |
| Canonical tail / collision / wave engine | 194 |
| Four-power / common-two arithmetic engine | 193 |
| Exponent-prefix / trit obstruction engine | 62 |
| Carry / affine information-state engine | 27 |
| Ternary digit arithmetic engine | 17 |
| Certificate / provider / bridge layer | 16 |
| Custom tactic / automation layer | 11 |
| Total non-GST theorem-like declarations | 1,315 |

## Interpretation

`GST` should not be used as a blanket label for the entire theorem universe.

General Space Theory proper is one major family inside the project. The live proof stack also contains separate theorem engines: final Problem406 endpoint machinery, canonical tail/collision/wave machinery, four-power/common-two arithmetic, exponent-prefix/trit obstruction, carry/affine information-state lemmas, ternary digit arithmetic, certificate/provider/bridge machinery, and custom tactic automation.
