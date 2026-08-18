#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
Q3_ROOT="$ROOT/q3.lean.aristotle"

if [[ $# -eq 0 ]]; then
  targets=(
    "Q3/Proofs/PSD_CenteredCardinalBSpline.lean"
    "Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean"
    "Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean"
  )
else
  targets=("$@")
fi

cd "$Q3_ROOT"

if [[ -f "$ROOT/.venv/bin/activate" ]]; then
  # shellcheck disable=SC1091
  source "$ROOT/.venv/bin/activate"
elif [[ -f ".venv/bin/activate" ]]; then
  # shellcheck disable=SC1091
  source ".venv/bin/activate"
fi

for target in "${targets[@]}"; do
  if [[ "$target" == q3.lean.aristotle/* ]]; then
    target="${target#q3.lean.aristotle/}"
  fi
  if [[ "$target" == ./* ]]; then
    target="${target#./}"
  fi

  echo "lean $target"
  lake env lean "$target"

  echo "scan $target"
  if rg -n 'sorry|exact\?|admit' "$target"; then
    echo "hole marker found in $target" >&2
    exit 1
  fi

  if git -C "$ROOT" diff -- "$Q3_ROOT/$target" | rg -n '^\+.*\baxiom\b'; then
    echo "new axiom in diff for $target" >&2
    exit 1
  fi
done

echo "q3_check ok"
