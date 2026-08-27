#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
Q3_ROOT="$ROOT/q3.lean.aristotle"

modules=(
  Q3.Axioms
  Q3.A3_Bridge
  Q3.Proofs.Q_nonneg_on_atoms_integrated
  Q3.Clean.AxiomsTier1
  Q3.Proofs.Q_Lipschitz_Bridge
  Q3.ProofsIntegrated
  Q3.AxiomsTheorems
  Q3.CheckAxioms
)

non_axiom_files=(
  q3.lean.aristotle/Q3/A3_Bridge.lean
  q3.lean.aristotle/Q3/Proofs/Q_nonneg_on_atoms_integrated.lean
  q3.lean.aristotle/Q3/Proofs/Q_Lipschitz_Bridge.lean
  q3.lean.aristotle/Q3/ProofsIntegrated.lean
  q3.lean.aristotle/Q3/AxiomsTheorems.lean
  q3.lean.aristotle/Q3/CheckAxioms.lean
)

lean_stdin() {
  env -u LD_LIBRARY_PATH lake env lean --stdin
}

axioms_for() {
  local import_module="$1"
  local declaration="$2"
  printf '%s\n' "import $import_module" "#print axioms $declaration" \
    | lean_stdin \
    | sed -E "1s/'[^']+'/'DECLARATION'/"
}

assert_axiom_profile_parity() {
  local import_module="$1"
  local old_name="$2"
  local canonical_name="$3"
  local old_profile canonical_profile
  old_profile="$(axioms_for "$import_module" "$old_name")"
  canonical_profile="$(axioms_for "$import_module" "$canonical_name")"
  if [[ "$old_profile" != "$canonical_profile" ]]; then
    printf 'axiom-profile mismatch: %s vs %s\n' "$old_name" "$canonical_name" >&2
    diff -u <(printf '%s\n' "$old_profile") <(printf '%s\n' "$canonical_profile") >&2 || true
    return 1
  fi
}

assert_deprecated_term_fails() {
  local import_module="$1"
  local term="$2"
  local exact_type="$3"
  local output
  if output="$(printf '%s\n' \
      "import $import_module" \
      'set_option warningAsError true' \
      "example : $exact_type := $term" \
      | lean_stdin 2>&1)"; then
    printf 'deprecated term unexpectedly passed warningAsError: %s\n' "$term" >&2
    return 1
  fi
  if ! rg -q 'has been deprecated' <<<"$output"; then
    printf 'deprecated term failed for the wrong reason: %s\n%s\n' "$term" "$output" >&2
    return 1
  fi
}

assert_consumer_paths() {
  local token="$1"
  local expected="$2"
  local actual
  actual="$(git -C "$ROOT" grep -l -F "$token" -- '*.lean' 2>/dev/null | sort || true)"
  if [[ "$actual" != "$expected" ]]; then
    printf 'tracked consumer/provenance set drift for %s\n' "$token" >&2
    diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") >&2 || true
    return 1
  fi
}

assert_bare_token_occurrences() {
  local token="$1"
  local expected="$2"
  local actual
  actual="$(git -C "$ROOT" grep -n -E "(^|[^.[:alnum:]_])${token}([^[:alnum:]_]|$)" \
    -- q3.lean.aristotle/Q3 \
    2>/dev/null | sort || true)"
  if [[ "$actual" != "$expected" ]]; then
    printf 'active Q3 bare-token occurrence set drift for %s\n' "$token" >&2
    diff -u <(printf '%s\n' "$expected") <(printf '%s\n' "$actual") >&2 || true
    return 1
  fi
}

cd "$Q3_ROOT"

printf 'build %s\n' "${modules[*]}"
env -u LD_LIBRARY_PATH lake build "${modules[@]}"

for module in "${modules[@]}"; do
  file="${module//./\/}.lean"
  printf 'lean %s\n' "$file"
  env -u LD_LIBRARY_PATH lake env lean "$file"
done

printf 'standard q3_check on non-axiom files\n'
env -u LD_LIBRARY_PATH bash "$ROOT/scripts/q3_check.sh" "${non_axiom_files[@]}"

printf 'exact old/new statement parity\n'
printf '%s\n' \
  'import Q3.Axioms' \
  'import Q3.Clean.AxiomsTier1' \
  'set_option warningAsError false' \
  'example : (∀ K : ℝ, K > 0 → Q3.c_arch K > 0) := Q3.c_arch_pos' \
  'example : (∀ K : ℝ, K > 0 → Q3.c_arch K > 0) := Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption' \
  'example : (∀ K : ℝ, K ≥ 1 → Q3.c_star ≤ Q3.c_arch K) := Q3.c_star_le_c_arch' \
  'example : (∀ K : ℝ, K ≥ 1 → Q3.c_star ≤ Q3.c_arch K) := Q3.Conditional.LegacyArchFloor.torusFloorLeRawKernelCompactInfAssumption' \
  'example : (∀ ξ : ℝ, Q3.a_star ξ > 0) := Q3.Clean.a_star_pos' \
  'example : (∀ ξ : ℝ, Q3.a_star ξ > 0) := Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption' \
  'example : (∀ K : ℝ, K > 0 → Q3.Clean.c_arch K > 0) := Q3.Clean.c_arch_pos' \
  'example : (∀ K : ℝ, K > 0 → Q3.Clean.c_arch K > 0) := Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption' \
  | lean_stdin >/dev/null

printf 'exact old/new axiom-profile parity\n'
assert_axiom_profile_parity Q3.Axioms \
  Q3.c_arch_pos \
  Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption
assert_axiom_profile_parity Q3.Axioms \
  Q3.c_star_le_c_arch \
  Q3.Conditional.LegacyArchFloor.torusFloorLeRawKernelCompactInfAssumption
assert_axiom_profile_parity Q3.Clean.AxiomsTier1 \
  Q3.Clean.a_star_pos \
  Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption
assert_axiom_profile_parity Q3.Clean.AxiomsTier1 \
  Q3.Clean.c_arch_pos \
  Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption

printf 'exact canonical assumption source set\n'
actual_assumptions="$({
  awk '/^axiom (rawKernel|torusFloor)/ {print FILENAME ":" $2}' \
    Q3/Axioms.lean Q3/Clean/AxiomsTier1.lean
} | sort)"
expected_assumptions="$(printf '%s\n' \
  'Q3/Axioms.lean:rawKernelCompactInfPosAssumption' \
  'Q3/Axioms.lean:torusFloorLeRawKernelCompactInfAssumption' \
  'Q3/Clean/AxiomsTier1.lean:rawKernelCompactInfPosAssumption' \
  'Q3/Clean/AxiomsTier1.lean:rawKernelGlobalPosAssumption' \
  | sort)"
if [[ "$actual_assumptions" != "$expected_assumptions" ]]; then
  printf 'canonical assumption source set drift\n' >&2
  diff -u <(printf '%s\n' "$expected_assumptions") \
    <(printf '%s\n' "$actual_assumptions") >&2 || true
  exit 1
fi

printf 'exact audited axiom-module content hashes\n'
expected_axioms_sha='ac2523639ae52cebf323a08ebcb01394094d3fd39d8abd6185af28c810f50b2a'
expected_clean_sha='98df0d9bc0c9d8fee63e3c916be0f4f6cb72d596d985421a5db3831768d000c5'
actual_axioms_sha="$(sha256sum Q3/Axioms.lean | cut -d' ' -f1)"
actual_clean_sha="$(sha256sum Q3/Clean/AxiomsTier1.lean | cut -d' ' -f1)"
[[ "$actual_axioms_sha" == "$expected_axioms_sha" ]] || {
  printf 'Q3/Axioms.lean content drift: %s\n' "$actual_axioms_sha" >&2
  exit 1
}
[[ "$actual_clean_sha" == "$expected_clean_sha" ]] || {
  printf 'Q3/Clean/AxiomsTier1.lean content drift: %s\n' "$actual_clean_sha" >&2
  exit 1
}

printf 'deprecated aliases expected-fail under warningAsError\n'
assert_deprecated_term_fails Q3.Axioms Q3.c_arch_pos \
  '(∀ K : ℝ, K > 0 → Q3.c_arch K > 0)'
assert_deprecated_term_fails Q3.Axioms Q3.c_star_le_c_arch \
  '(∀ K : ℝ, K ≥ 1 → Q3.c_star ≤ Q3.c_arch K)'
assert_deprecated_term_fails Q3.Clean.AxiomsTier1 Q3.Clean.a_star_pos \
  '(∀ ξ : ℝ, Q3.a_star ξ > 0)'
assert_deprecated_term_fails Q3.Clean.AxiomsTier1 Q3.Clean.c_arch_pos \
  '(∀ K : ℝ, K > 0 → Q3.Clean.c_arch K > 0)'

printf 'canonical names warning-clean\n'
printf '%s\n' \
  'import Q3.Axioms' \
  'import Q3.Clean.AxiomsTier1' \
  'set_option warningAsError true' \
  'example : (∀ K : ℝ, K > 0 → Q3.c_arch K > 0) := Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption' \
  'example : (∀ K : ℝ, K ≥ 1 → Q3.c_star ≤ Q3.c_arch K) := Q3.Conditional.LegacyArchFloor.torusFloorLeRawKernelCompactInfAssumption' \
  'example : (∀ ξ : ℝ, Q3.a_star ξ > 0) := Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption' \
  'example : (∀ K : ℝ, K > 0 → Q3.Clean.c_arch K > 0) := Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption' \
  | lean_stdin >/dev/null

printf 'current RH axiom profile\n'
rh_profile="$(printf '%s\n' \
  'import Q3.Main' \
  '#print axioms Q3.Main.RH_of_Weil_and_Q3' \
  | lean_stdin | tr -d '[:space:]')"
expected_rh_profile="'Q3.Main.RH_of_Weil_and_Q3'dependsonaxioms:[propext,Classical.choice,Q3.Weil_criterion,Q3.prime_term_le_at_t_critical_axiom,Quot.sound]"
if [[ "$rh_profile" != "$expected_rh_profile" ]]; then
  printf 'current RH axiom profile drift\n%s\n' "$rh_profile" >&2
  exit 1
fi

printf 'P_A import-scope plants\n'
printf '%s\n' \
  'import Q3.AxiomsTheorems' \
  'set_option warningAsError true' \
  '#check P_A' \
  | lean_stdin >/dev/null
pa_failure="$(printf '%s\n' \
  'import Q3.AxiomsTheorems' \
  '#check Q3.P_A' \
  | lean_stdin 2>&1 || true)"
if ! rg -q 'Unknown identifier `Q3.P_A`' <<<"$pa_failure"; then
  printf 'Q3.P_A expected-fail plant did not fire\n%s\n' "$pa_failure" >&2
  exit 1
fi

printf 'tracked deprecated-name consumer/provenance census\n'
assert_consumer_paths Q3.c_arch_pos "$(printf '%s\n' \
  'q3.lean.aristotle/A3_Bridge.lean' \
  'q3.lean.aristotle/AxiomsTheorems.lean' \
  'q3.lean.aristotle/CheckAxioms.lean' \
  'q3.lean.aristotle/Proofs/Q_nonneg_bridge.lean' \
  'q3.lean.aristotle/Proofs/Q_nonneg_on_atoms_integrated.lean' \
  'q3.lean.aristotle/archive/untracked_misc_2026-01-20/full/q3.lean.aristotle/archive/bridge_wip_2026-01-20/Q_Nonneg_Bridge.lean' \
  'q3.lean.aristotle/aristotle_output/Brange_Lipschitz_HeatProof_aristotle.lean' \
  'q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctx24.lean' \
  'q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctxrootfix.lean' | sort)"
assert_consumer_paths Q3.c_star_le_c_arch "$(printf '%s\n' \
  'q3.lean.aristotle/aristotle_output/Brange_Lipschitz_HeatProof_aristotle.lean' \
  'q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctx24.lean' \
  'q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctxrootfix.lean' | sort)"
assert_consumer_paths Q3.Clean.a_star_pos \
  'q3.lean.aristotle/Proofs/Q_Lipschitz_bridge_v2.lean
q3.lean.aristotle/archive/bridge_legacy_lowercase_2026-01-20/Q_Lipschitz_bridge.lean'
assert_consumer_paths Q3.Clean.c_arch_pos ''

printf 'active Q3 bare-name census\n'
assert_bare_token_occurrences c_arch_pos "$(printf '%s\n' \
  'q3.lean.aristotle/Q3/Axioms.lean:295:theorem c_arch_pos : ∀ K : ℝ, K > 0 → c_arch K > 0 :=' \
  'q3.lean.aristotle/Q3/Clean/AxiomsTier1.lean:111:theorem c_arch_pos : ∀ K : ℝ, K > 0 → c_arch K > 0 :=' | sort)"
assert_bare_token_occurrences c_star_le_c_arch \
  'q3.lean.aristotle/Q3/Axioms.lean:343:theorem c_star_le_c_arch : ∀ K : ℝ, K ≥ 1 → c_star ≤ c_arch K :='
assert_bare_token_occurrences a_star_pos "$(printf '%s\n' \
  'q3.lean.aristotle/Q3/Axioms.lean:118:theorem a_star_pos : a_star 0 > 0 := by' \
  'q3.lean.aristotle/Q3/Axioms.lean:743:#check a_star_pos' \
  'q3.lean.aristotle/Q3/Clean/AxiomsTier1.lean:53:theorem a_star_pos : ∀ ξ : ℝ, Q3.a_star ξ > 0 :=' \
  'q3.lean.aristotle/Q3/Proofs/A_Star_Properties.lean:13:- a_star_pos (T1.3): requires digamma positivity bounds' \
  'q3.lean.aristotle/Q3/Proofs/A_Star_Properties.lean:323:/-! ## Note on a_star_pos' \
  'q3.lean.aristotle/Q3/Proofs/A_Star_Properties.lean:325:The theorem `a_star_pos : a_star 0 > 0` is now proven in Q3/Axioms.lean' \
  'q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean:68:/-- M_a_local K > 0 (follows from a_star_pos and nonemptiness) -/' \
  'q3.lean.aristotle/Q3/Proofs/Q_Lipschitz.lean:72:  have h_pos : |a_star 0| > 0 := abs_pos.mpr (ne_of_gt a_star_pos)' \
  'q3.lean.aristotle/Q3/Proofs/Q_Lipschitz_arch_bridge.lean:63:  have h_pos : |a_star 0| > 0 := abs_pos.mpr (ne_of_gt a_star_pos)' \
  'q3.lean.aristotle/Q3/Tier2_Verification.lean:67:# Note: Uses Tier-1 axioms a_star_pos, a_star_bdd_on_compact (acceptable)' | sort)"

printf 'Route B proof-subtree zero-diff\n'
if [[ -n "$(git -C "$ROOT" status --porcelain -- q3.lean.aristotle/Q3/Proofs/RouteB)" ]]; then
  printf 'Route B proof subtree changed\n' >&2
  exit 1
fi

printf 'ARCH_FLOOR_SEMANTIC_QUARANTINE_VALID\n'
