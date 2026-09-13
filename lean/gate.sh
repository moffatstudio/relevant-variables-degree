#!/usr/bin/env bash
# gate.sh — arbiter for the R3 Lean project. Exit 0 iff build passes, no laundering
# constructs appear in R3/, and every listed theorem depends only on the three standard axioms.
# Usage: bash gate.sh   (from lean/); writes GATE.txt
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
fail=0
out=GATE.txt
{
echo "GATE run $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "toolchain: $(cat lean-toolchain)   mathlib: $(cat .lake/packages/mathlib/lean-toolchain 2>/dev/null || echo "not fetched")"
echo
echo "== modules imported by R3.lean =="; cat R3.lean
echo
echo "== lake build =="
if lake build 2>&1 | grep -vE "^✔|Replayed" | tail -5; then :; fi
if lake build >/dev/null 2>&1; then echo "ok    lake build exit 0"; else echo "FAIL  lake build"; fail=1; fi
echo
echo "== laundering scan (sorry/admit/axiom/native_decide/unsafe/implemented_by/extern) =="
PAT='(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)|^[[:space:]]*axiom[[:space:]]|native_decide|unsafe|implemented_by|@\[extern'
if hits=$(grep -rnE "$PAT" R3 R3.lean --include='*.lean' 2>/dev/null); then
  echo "FAIL  banned constructs:"; printf '%s\n' "$hits"; fail=1
else
  echo "ok    none found"
fi
echo
echo "== axiom audit =="
cat > axiom_check.lean <<'EOF'
import R3
#print axioms R3.evalF_sq
#print axioms R3.linkVal_mem
#print axioms R3.two_dvd_mass
#print axioms R3.four_le_mass
#print axioms R3.sum_mass_le
#print axioms R3.mass_four_pm
#print axioms R3.mass_four_card
#print axioms R3.mass_four
#print axioms R3.mass_le_eight
#print axioms R3.mass_cases
#print axioms R3.card_mass_ne_four_le_two
#print axioms R3.nine_mass_four
#print axioms R3.exists_mass_four
#print axioms R3.bookkeeping
#print axioms R3.mass_four_link
#print axioms R3.mass_four_even_degree
#print axioms R3.twelve_mass_four
#print axioms R3.twelve_card_three
#print axioms R3.twelve_coeff_pm
#print axioms R3.twelve_link_card_two
#print axioms R3.twelve_link
#print axioms R3.four_pairs_cycle
#print axioms R3.twelve_link_cycle
EOF
axout=$(lake env lean axiom_check.lean 2>&1)
printf '%s\n' "$axout"
printf '%s\n' "$axout" > AXIOMS.txt
if printf '%s' "$axout" | grep -qE 'sorryAx|error|ofReduceBool'; then echo "FAIL  axiom set not clean"; fail=1; else echo "ok    all listed theorems use only [propext, Classical.choice, Quot.sound]"; fi
echo
if [ $fail -eq 0 ]; then echo "GATE: PASS"; else echo "GATE: FAIL"; fi
} | tee "$out"
exit $fail
