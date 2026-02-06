#!/usr/bin/env bash
# Run heavy workloads in an isolated user slice to protect GUI session stability.
# Usage:
#   ./scripts/run_heavy.sh
#   ./scripts/run_heavy.sh <command> [args...]

set -euo pipefail

SLICE_NAME="${HEAVY_SLICE_NAME:-codex-heavy.slice}"
MEM_HIGH="${HEAVY_MEM_HIGH:-20G}"
MEM_MAX="${HEAVY_MEM_MAX:-28G}"
CPU_WEIGHT="${HEAVY_CPU_WEIGHT:-80}"
OOM_PREF="${HEAVY_OOM_PREF:-avoid}"

usage() {
  cat <<'EOF'
Usage:
  ./scripts/run_heavy.sh
  ./scripts/run_heavy.sh <command> [args...]

Behavior:
  - Ensures user slice "codex-heavy.slice" exists with safe defaults.
  - Runs command inside this slice via systemd-run --user --scope.
  - With no command, starts interactive bash in the isolated slice.

Optional env overrides:
  HEAVY_SLICE_NAME (default: codex-heavy.slice)
  HEAVY_MEM_HIGH   (default: 20G)
  HEAVY_MEM_MAX    (default: 28G)
  HEAVY_CPU_WEIGHT (default: 80)
  HEAVY_OOM_PREF   (default: avoid)
EOF
}

ensure_user_systemd() {
  if ! systemctl --user show-environment >/dev/null 2>&1; then
    echo "Error: user systemd instance is not available." >&2
    exit 1
  fi
}

ensure_slice() {
  local unit_dir unit_path
  unit_dir="${HOME}/.config/systemd/user"
  unit_path="${unit_dir}/${SLICE_NAME}"

  mkdir -p "${unit_dir}"

  if [[ ! -f "${unit_path}" ]]; then
    cat > "${unit_path}" <<EOF
[Unit]
Description=Isolated slice for heavy codex/lean workloads

[Slice]
MemoryHigh=${MEM_HIGH}
MemoryMax=${MEM_MAX}
CPUWeight=${CPU_WEIGHT}
ManagedOOMPreference=${OOM_PREF}
EOF
    echo "Created ${unit_path}"
    systemctl --user daemon-reload
  fi

  systemctl --user start "${SLICE_NAME}"
}

main() {
  if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
    usage
    exit 0
  fi

  ensure_user_systemd
  ensure_slice

  if [[ "$#" -eq 0 ]]; then
    exec systemd-run --user --scope -p Slice="${SLICE_NAME}" bash
  fi

  exec systemd-run --user --scope -p Slice="${SLICE_NAME}" "$@"
}

main "$@"

