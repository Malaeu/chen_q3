#!/usr/bin/env bash
set -euo pipefail

# Sequentially build GT10000 shard modules for PrimePowAuto,
# resumable by existing .olean artifacts.
#
# Usage:
#   ./scripts/build_primepow_gt10000_sequential.sh
#   ./scripts/build_primepow_gt10000_sequential.sh --from 300001
#   ./scripts/build_primepow_gt10000_sequential.sh --timeout 1800

FROM=10001
TIMEOUT_SECS=3600

while [[ $# -gt 0 ]]; do
  case "$1" in
    --from)
      FROM="${2:?missing value for --from}"
      shift 2
      ;;
    --timeout)
      TIMEOUT_SECS="${2:?missing value for --timeout}"
      shift 2
      ;;
    *)
      echo "Unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

if [[ ! -d q3.lean.aristotle ]]; then
  echo "Run from repo root (q3.lean.aristotle directory is required)." >&2
  exit 2
fi

if (( FROM < 10001 || FROM > 990001 )); then
  echo "--from must be in [10001, 990001]" >&2
  exit 2
fi

# Align to shard boundary 10001 + k*10000
if (((FROM - 10001) % 10000 != 0)); then
  echo "--from must be 10001 + k*10000 (e.g. 10001, 20001, 30001 ...)" >&2
  exit 2
fi

cd q3.lean.aristotle

if [[ ! -f .venv/bin/activate ]]; then
  echo "Missing .venv activate script: q3.lean.aristotle/.venv/bin/activate" >&2
  exit 2
fi

source .venv/bin/activate

if ! command -v lake >/dev/null 2>&1; then
  echo "lake is not available in PATH after venv activation" >&2
  exit 2
fi

STAMP="$(date +%Y%m%d_%H%M%S)"
LOG_DIR="../tmp/primepow_gt10000_logs"
mkdir -p "${LOG_DIR}"
LOG_FILE="${LOG_DIR}/build_${STAMP}.log"

echo "Log: ${LOG_FILE}"
echo "From shard lower bound: ${FROM}"
echo "Per-shard timeout: ${TIMEOUT_SECS}s"

for ((lo=FROM; lo<=990001; lo+=10000)); do
  hi=$((lo + 9999))
  mod="Q3.Proofs.PrimeCert.BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_${lo}_${hi}"
  olean=".lake/build/lib/lean/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_PrimePowAutoGT10000_${lo}_${hi}.olean"

  if [[ -f "${olean}" ]]; then
    echo "[skip] ${mod} (already built)" | tee -a "${LOG_FILE}"
    continue
  fi

  echo "[build] ${mod}" | tee -a "${LOG_FILE}"
  if ! timeout "${TIMEOUT_SECS}" lake build "+${mod}:olean" >>"${LOG_FILE}" 2>&1; then
    echo "[fail] ${mod} (timeout or build error)" | tee -a "${LOG_FILE}"
    exit 1
  fi

  if [[ ! -f "${olean}" ]]; then
    echo "[fail] ${mod} finished without expected artifact: ${olean}" | tee -a "${LOG_FILE}"
    exit 1
  fi

  echo "[ok] ${mod}" | tee -a "${LOG_FILE}"
done

echo "[done] all GT10000 shards built" | tee -a "${LOG_FILE}"
