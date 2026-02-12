#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "${ROOT_DIR}"

LOG="${1:-}"
if [[ -z "${LOG}" ]]; then
  LOG="$(ls -1t tmp/primepow_gt10000_logs/build_*.log 2>/dev/null | head -n 1 || true)"
fi

if [[ -z "${LOG}" || ! -f "${LOG}" ]]; then
  echo "[ERROR] Не найден лог build_*.log в tmp/primepow_gt10000_logs" >&2
  exit 1
fi

first_build_line="$(rg '^\[build\]' "${LOG}" | head -n 1 || true)"
if [[ -z "${first_build_line}" ]]; then
  echo "[ERROR] В логе нет строк [build]: ${LOG}" >&2
  exit 1
fi

if [[ "${first_build_line}" =~ _([0-9]+)_([0-9]+)$ ]]; then
  FROM="${BASH_REMATCH[1]}"
else
  FROM=10001
fi

TOTAL=$(( (990001 - FROM) / 10000 + 1 ))
OK_COUNT="$(rg -c '^\[ok\]' "${LOG}" || echo 0)"
BUILD_COUNT="$(rg -c '^\[build\]' "${LOG}" || echo 0)"
FAIL_COUNT="$(rg -c '^\[fail\]' "${LOG}" || echo 0)"
DONE_COUNT="$(rg -c '^\[done\]' "${LOG}" || echo 0)"

START_EPOCH="$(stat -c %W "${LOG}" 2>/dev/null || echo -1)"
if [[ "${START_EPOCH}" -le 0 ]]; then
  # fallback if birth time is unavailable
  START_EPOCH="$(date +%s)"
fi
NOW_EPOCH="$(date +%s)"
ELAPSED=$(( NOW_EPOCH - START_EPOCH ))

if [[ "${OK_COUNT}" -gt 0 ]]; then
  AVG_PER_SHARD=$(( ELAPSED / OK_COUNT ))
  REM=$(( TOTAL - OK_COUNT ))
  ETA=$(( REM * AVG_PER_SHARD ))
else
  AVG_PER_SHARD=0
  ETA=0
fi

CURRENT_SHARD="$(rg '^\[build\]' "${LOG}" | tail -n 1 | sed -E 's/^\[build\] .*PrimePowAutoGT10000_([0-9]+_[0-9]+)$/\1/' || true)"
if [[ -z "${CURRENT_SHARD}" ]]; then
  CURRENT_SHARD="не определён"
fi

latest_scope="$(
  systemctl --user list-units --type=scope --all --no-legend 2>/dev/null \
    | rg 'run-.*build_primepow_gt10000_sequential\.sh' \
    | awk '{print $1}' \
    | tail -n 1 \
    || true
)"

echo "Лог: ${LOG}"
echo "Текущий шард: ${CURRENT_SHARD}"
echo "Готово: ${OK_COUNT}/${TOTAL} (build=${BUILD_COUNT}, fail=${FAIL_COUNT}, done=${DONE_COUNT})"
echo "Прошло: $((ELAPSED/3600))ч $(((ELAPSED%3600)/60))м"

if [[ "${AVG_PER_SHARD}" -gt 0 ]]; then
  echo "Среднее на шард: $((AVG_PER_SHARD/3600))ч $(((AVG_PER_SHARD%3600)/60))м"
  echo "Осталось (оценка): $((ETA/3600))ч $(((ETA%3600)/60))м (~$((ETA/86400))д)"
else
  echo "Среднее/ETA: недостаточно данных (нет ни одного [ok])."
fi

if [[ -n "${latest_scope}" ]]; then
  echo "Активный scope: ${latest_scope}"
  systemctl --user show "${latest_scope}" -p ActiveState -p MemoryCurrent -p TasksCurrent
else
  echo "Активный scope: не найден"
fi
