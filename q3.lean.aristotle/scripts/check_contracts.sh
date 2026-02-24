#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "[check-contracts] build + no-sorry on sanity module"
lake env lean -Dwarn.sorry=true -EhasSorry Q3/CheckContracts.lean

echo "[check-contracts] axioms snapshot (fast path)"
Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh

echo "[check-contracts] ok"
