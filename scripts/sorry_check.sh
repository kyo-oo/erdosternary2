#!/usr/bin/env bash
# sorry_check.sh — V5 verification gate
#
# Counts `sorry` tactic occurrences in project .lean files (whole-word match,
# so `sorry_check` / strings containing "sorry" don't false-positive).
# Excludes backups (*.bak*) and the .lake/ build cache.
#
# MUST return 0 (zero sorries) BEFORE the comparator is run.
# (V5 §15 rule 70: never recommend running the comparator when sorries exist.)

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT_DIR"

# Whole-word grep for the `sorry` tactic, excluding backups and .lake cache.
SORRY_LINES=$(grep -rwn 'sorry' --include='*.lean' . 2>/dev/null \
  | grep -v '\.bak' \
  | grep -v '/\.lake/' \
  || true)

if [ -z "$SORRY_LINES" ]; then
  echo "sorry_check: 0 sorries found ✓"
  exit 0
else
  SORRY_COUNT=$(printf '%s\n' "$SORRY_LINES" | wc -l | tr -d ' ')
  echo "sorry_check: $SORRY_COUNT sorry(s) found ✗"
  echo "$SORRY_LINES"
  exit 1
fi
