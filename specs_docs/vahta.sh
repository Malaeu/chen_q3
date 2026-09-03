#!/usr/bin/env bash
# vahta.sh — origin watch that DIES when the event happens (its exit is the wake-up kick).
#
# Usage:
#   specs_docs/vahta.sh --path <repo-relative file>   [--delay S] [--every S] [--max S] [--branch B]
#   specs_docs/vahta.sh --ahead                        [--delay S] [--every S] [--max S] [--branch B]
#
#   --path   exit 0 with NEW_ON_ORIGIN as soon as the file exists on origin/<branch>
#            (use for a judge verdict: the EXPECTED_VERDICT_PATH of the request)
#   --ahead  exit 0 with ORIGIN_AHEAD as soon as origin/<branch> has commits not in local HEAD
#            (own pushes do not wake it: the condition is "origin ahead of HEAD", not "hash changed")
#   --delay  initial sleep before the first check (default 0; judge answers take ~15-20 min → 900)
#   --every  poll period in seconds (default 60)
#   --max    give up after this many seconds, exit 2 with TIMEOUT (default 7200)
#
# Run it as a BACKGROUND task from the harness; the harness re-invokes the body when it exits.
# Self-match safety: this script never uses pgrep/ps on its own command line; the wake-up is
# the process exit, not a process search (field lesson 2026-09-03: `pgrep -f <pattern>` inside
# a loop matches the loop's own shell and never exits).
set -u
PATH_REL=""; MODE=""; DELAY=0; EVERY=60; MAX=7200; BRANCH="rh_clean"
while [ $# -gt 0 ]; do
  case "$1" in
    --path) MODE=path; PATH_REL="$2"; shift 2;;
    --ahead) MODE=ahead; shift;;
    --delay) DELAY="$2"; shift 2;;
    --every) EVERY="$2"; shift 2;;
    --max) MAX="$2"; shift 2;;
    --branch) BRANCH="$2"; shift 2;;
    *) echo "vahta: unknown arg $1" >&2; exit 64;;
  esac
done
[ -n "$MODE" ] || { echo "vahta: need --path <file> or --ahead" >&2; exit 64; }
cd "$(git rev-parse --show-toplevel)" || exit 65
echo "[vahta $(date +%H:%M:%S)] armed mode=$MODE branch=$BRANCH delay=${DELAY}s every=${EVERY}s max=${MAX}s ${PATH_REL}"
sleep "$DELAY"
START=$(date +%s)
while :; do
  git fetch -q origin "$BRANCH" 2>/dev/null
  if [ "$MODE" = path ]; then
    if git cat-file -e "origin/$BRANCH:$PATH_REL" 2>/dev/null; then
      echo "NEW_ON_ORIGIN $PATH_REL"; git log --oneline -1 "origin/$BRANCH"; exit 0
    fi
  else
    N=$(git rev-list --count "HEAD..origin/$BRANCH" 2>/dev/null || echo 0)
    if [ "${N:-0}" -gt 0 ]; then
      echo "ORIGIN_AHEAD $N"; git log --oneline "HEAD..origin/$BRANCH" | head -5; exit 0
    fi
  fi
  NOW=$(date +%s)
  if [ $((NOW-START)) -ge "$MAX" ]; then echo "TIMEOUT after ${MAX}s"; exit 2; fi
  sleep "$EVERY"
done
