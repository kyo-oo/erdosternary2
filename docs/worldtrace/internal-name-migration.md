# Worldtrace internal-name migration plan

This is the dependency-safe plan for removing historical/tool-era names from live source.

## Current position

Worldtrace Arithmetic now has a public facade and layer modules.  The checked proof corpus remains stable underneath.

The next migration target is not mathematical content.  It is presentation hygiene:

- old `gpt56*` declaration names;
- old tool-era comments;
- construction-history names that should not appear in public-facing theorem surfaces;
- workflow names that still contain historical implementation labels.

## Rule

Do not mass-rename the proof corpus blindly.

A direct rename can break dependent declarations across the monolith, imported modules, FINISHER copies, scripts, docs, and CI.  The migration must be staged.

## Stage A — audit

Generate a manifest of every historical identifier with:

- file path;
- line number;
- declaration kind;
- declaration name;
- whether the file is in the live import closure;
- whether the name is exported through any public API;
- suggested neutral replacement.

## Stage B — public neutral names

For important declarations, add clean wrappers first under:

```lean
Worldtrace.Genesis
Worldtrace.Ternary
Worldtrace.Carry
Worldtrace.Residue
Worldtrace.FourPower
Worldtrace.Navigation
Worldtrace.Collision
Worldtrace.Phase
Worldtrace.Certificate
```

This stage is already started.

## Stage C — internal aliases

Inside active source files, introduce neutral names beside historical names.

Example pattern:

```lean
/-- Neutral public/internal name. -/
theorem phase_cycle_shared_information := old_historical_name

/-- Deprecated compatibility alias. -/
theorem old_historical_name := phase_cycle_shared_information
```

Use this pattern only when the old name can safely become an alias without circularity.

## Stage D — reference rewrite

Rewrite references file-by-file from old names to neutral names.

After each cluster:

```bash
lake build Worldtrace.TheoremMap
lake build GST.PublicAPI
lake build ErdosTernary2
```

## Stage E — compatibility sunset

Only after full CI is green:

- remove obsolete aliases;
- update docs and generated manifests;
- freeze a release tag.

## Priority clusters

| Priority | Cluster | Reason |
| ---: | --- | --- |
| 1 | Public docs and README | First impression. |
| 2 | Worldtrace wrapper modules | Safe, compile-checked, no proof-body changes. |
| 3 | Active non-archive comments | Low risk. |
| 4 | Active declaration names used in public paths | High value, moderate risk. |
| 5 | Internal declaration names with many dependencies | High risk; requires graph-guided rewrite. |
| 6 | Archive/snapshot files | Preserve or quarantine; do not rewrite by default. |

## Release criterion

The migration is complete when:

1. `Worldtrace.TheoremMap` builds;
2. `Worldtrace.PublicAPI` builds;
3. `GST.PublicAPI` compatibility remains green;
4. the monolith proof body is unchanged unless a proof-specific task is approved;
5. no historical tool-era name is exported through the public API;
6. remaining historical names are either internal compatibility aliases or archived proof archaeology.
