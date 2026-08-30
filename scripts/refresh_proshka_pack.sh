#!/bin/sh
set -eu

printf '%s\n' \
  'PROSHKA_JANUARY_PACK_REFRESH_DISABLED' \
  'PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md is historical evidence only.' \
  'For optional read-only evidence use: python3 scripts/build_proshka_brief.py --mode tight' \
  'For an actual review request use the exact source-locked UTF-8 .txt plus:' \
  'python3 orchestrator/workflow_runtime.py review-plan --attachment <request.txt> --request-commit <commit> --request-id <id> --boundary-id <id> --expected-sha256 <sha256>' \
  >&2
exit 2
