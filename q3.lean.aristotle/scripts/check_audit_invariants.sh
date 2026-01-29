#!/usr/bin/env bash
set -euo pipefail

FULL_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
LEAN_ROOT="$FULL_ROOT/q3.lean.aristotle"

have_rg() {
  command -v rg >/dev/null 2>&1
}

search_fixed() {
  local pattern="$1"
  local file="$2"
  if have_rg; then
    rg -q -F "$pattern" "$file"
  else
    grep -q -F "$pattern" "$file"
  fi
}

fail=0
check() {
  local file="$1"
  local pattern="$2"
  local desc="$3"
  if ! search_fixed "$pattern" "$file"; then
    echo "missing: $desc ($file)"
    fail=1
  fi
}

check "$FULL_ROOT/sections/introduction.tex" "w_Q(n)=2\\Lambda(n)/\\sqrt{n}" "weights: w_Q"
check "$FULL_ROOT/sections/introduction.tex" "w_{\\mathrm{RKHS}}(n)=\\Lambda(n)/\\sqrt{n}" "weights: w_RKHS"
check "$FULL_ROOT/sections/scope_notation.tex" "\\(\\TT=\\RR/\\ZZ\\) with fundamental domain" "torus domain"
check "$FULL_ROOT/sections/scope_notation.tex" "\\xi_n=\\tfrac{\\log n}{2\\pi}" "node normalization"
check "$FULL_ROOT/sections/scope_notation.tex" "a_*(\\xi)" "a_star normalization"
check "$FULL_ROOT/sections/A3/rayleigh_bridge.tex" "p(\\xi_n)=\\sqrt{2M+1}" "prime_vec scaling"
check "$FULL_ROOT/sections/A3/rayleigh_bridge.tex" "(2M+1)\\,T_P^{(M)}" "prime block scaling"
check "$FULL_ROOT/sections/RKHS/core.tex" "M\\ge B" "span condition M >= B"
check "$FULL_ROOT/sections/A3/param_tables.tex" "legacy" "legacy constants note"
check "$LEAN_ROOT/docs/CHECKLIST_AUDIT_2026_01_17.md" "Addendum: normalization and chain guardrails" "audit addendum"
check "$LEAN_ROOT/Q3/Proofs/Rayleigh_Q_identification.lean" "2 * M + 1" "Lean scaling anchor"

if [[ "$fail" -ne 0 ]]; then
  echo "audit invariants: FAILED"
  exit 1
fi

echo "audit invariants: OK"
