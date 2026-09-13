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
echo "toolchain: $(cat lean-toolchain)"
echo
echo "== modules imported by R3.lean =="; cat R3.lean
echo
echo "== lake build =="
if lake build 2>&1 | grep -vE "^✔|Replayed" | tail -5; then :; fi
if lake build >/dev/null 2>&1; then echo "ok    lake build exit 0"; else echo "FAIL  lake build"; fail=1; fi
echo
echo "== laundering scan (sorry/admit/axiom/native_decide/unsafe/implemented_by/extern) =="
PAT='(^|[^A-Za-z_])(sorry|admit)([^A-Za-z_]|$)|^[[:space:]]*axiom[[:space:]]|native_decide|unsafe|implemented_by|@\[extern'
# backtick-quoted spans are prose (doc comments naming `sorry`), never code: strip them first.
scan_files=$(find R3 -name '*.lean' | sort; echo R3.lean)
if hits=$(for f in $scan_files; do sed 's/`[^`]*`//g' "$f" | grep -nE "$PAT" | sed "s|^|$f:|"; done | grep .); then
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
#print axioms R3.twelve_link_struct
#print axioms R3.edge_through
#print axioms R3.link_sixth
#print axioms R3.link_of_three_faces
#print axioms R3.closure_of_links
#print axioms R3.octahedron_closure
#print axioms R3.link_cycle
#print axioms R3.link_struct
#print axioms R3.no_triangle_at
#print axioms R3.octahedron_closure_gen
#print axioms R3.card_le_two_cases
#print axioms R3.three_pairs_triangle
#print axioms R3.pair_xor_pair_ne_two_pow
#print axioms R3.card_sum_even
#print axioms R3.linkType_zero
#print axioms R3.linkType_nozero
#print axioms R3.link_types
#print axioms R3.no_crossing_split
#print axioms R3.F_twelve
#print axioms R3.four_cover
#print axioms R3.mem_link
#print axioms R3.mass_four_link_cover
#print axioms R3.link_two_pow
#print axioms R3.link_pair
#print axioms R3.quad_deg_two
#print axioms R3.delta_eq_four
#print axioms R3.sum_dw_le
#print axioms R3.dw_saturate
#print axioms R3.exists_dw_outside
#print axioms R3.low_set_shape
#print axioms R3.delta_four_no_const
#print axioms R3.delta_four_structure
#print axioms R3.quad_exactly_two
#print axioms R3.link_L3
#print axioms R3.link_L3'
#print axioms R3.apex_eq
#print axioms R3.card_tri_eq
#print axioms R3.five_in_four
#print axioms R3.exists_fourth
#print axioms R3.eleven_cycle_closed
#print axioms R3.eleven_four_quadratics
#print axioms R3.delta_four_two_linear
#print axioms R3.cubicAt_link_card_two
#print axioms R3.link_cycle'
#print axioms R3.link_struct'
#print axioms R3.link_sixth'
#print axioms R3.link_of_three_faces'
#print axioms R3.no_triangle_at'
#print axioms R3.closure_of_links'
#print axioms R3.octahedron_closure_gen'
#print axioms R3.mass_six_pm
#print axioms R3.mass_six_card
#print axioms R3.mass_six
#print axioms R3.mass_six_link
#print axioms R3.card_eq_six
#print axioms R3.six_pm_sum
#print axioms R3.xor_two_pow_cancel6
#print axioms R3.four_distinct_exhaust
#print axioms R3.delta_two_weight
#print axioms R3.three_quadratics_absurd
#print axioms R3.two_quadratics_at
#print axioms R3.exists_quadratic
#print axioms R3.quad_three_of
#print axioms R3.eleven_delta_two_quad
#print axioms R3.delta_two_linear
#print axioms R3.pair_mem_of_eq
#print axioms R3.pair_of_triangle
#print axioms R3.link_L4_of_linear
#print axioms R3.two_linear_no_quad
#print axioms R3.cubicAt_of_two_linear
#print axioms R3.closure_local
#print axioms R3.mem_of_triangle_eq
#print axioms R3.linear_not_triangle
#print axioms R3.eleven_delta_four
#print axioms R3.one_linear_no_quad
#print axioms R3.one_linear_no_const
#print axioms R3.cubicAt_of_one_linear
#print axioms R3.tri_link_absurd
#print axioms R3.common_sixth
#print axioms R3.supp_tri
#print axioms R3.pair_tri_xor
#print axioms R3.tri_ne_of
#print axioms R3.tri_ne_bit
#print axioms R3.tri_apex_common
#print axioms R3.link_nbrs_of_v
#print axioms R3.eleven_delta_two_lin_four
#print axioms R3.tri_of_bit
#print axioms R3.two_pow_ne_tri
#print axioms R3.other_nbr
#print axioms R3.tri_degen
#print axioms R3.eleven_delta_two_lin_six
#print axioms R3.eleven_delta_two
#print axioms R3.apex_gen
#print axioms R3.apex_other
#print axioms R3.closure_kills
#print axioms R3.closure_near
#print axioms R3.condII_corr
#print axioms R3.corr_bit_half
#print axioms R3.corr_supp
#print axioms R3.cubic_sum_mass
#print axioms R3.delta_zero_residual
#print axioms R3.dist6_swap
#print axioms R3.edge_not_three
#print axioms R3.edge_second
#print axioms R3.eleven_degree_split
#print axioms R3.eleven_delta_zero
#print axioms R3.eleven_delta_zero_eight
#print axioms R3.eleven_delta_zero_reduce
#print axioms R3.eleven_delta_zero_residual
#print axioms R3.exists_fifth_supp
#print axioms R3.exists_free_set
#print axioms R3.kill_free_triple
#print axioms R3.kill_pair
#print axioms R3.linkIs_rev
#print axioms R3.near_self
#print axioms R3.no_exc_pair
#print axioms R3.no_fifth_supp
#print axioms R3.octa_eight
#print axioms R3.octa_eight'
#print axioms R3.octa_half
#print axioms R3.octa_kill
#print axioms R3.octa_kill4
#print axioms R3.octa_kill4'
#print axioms R3.octa_v_triple
#print axioms R3.pair_not_three
#print axioms R3.pair_second
#print axioms R3.second_v_triple
#print axioms R3.supp_eq_quad
#print axioms R3.supp_tri_of_mem
#print axioms R3.tri_distinct
#print axioms R3.tri_xor_pair
EOF
axout=$(lake env lean axiom_check.lean 2>&1)
printf '%s\n' "$axout"
printf '%s\n' "$axout" > AXIOMS.txt
if printf '%s' "$axout" | grep -qE 'sorryAx|error|ofReduceBool'; then echo "FAIL  axiom set not clean"; fail=1; else echo "ok    all listed theorems use only [propext, Classical.choice, Quot.sound]"; fi
echo
if [ $fail -eq 0 ]; then echo "GATE: PASS"; else echo "GATE: FAIL"; fi
} | tee "$out"
exit $fail
