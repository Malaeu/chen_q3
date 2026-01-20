#!/bin/bash
# Lean 4 TDD Helper Script
# Usage: ./scripts/tdd.sh <command> [args]

set -e
cd "$(dirname "$0")/.."

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

case "$1" in
  #═══════════════════════════════════════════════════════════════
  # RED: Add a new theorem with sorry
  #═══════════════════════════════════════════════════════════════
  red)
    if [ -z "$2" ] || [ -z "$3" ] || [ -z "$4" ]; then
      echo "Usage: ./scripts/tdd.sh red <name> \"<type>\" <file.lean>"
      echo "Example: ./scripts/tdd.sh red my_lemma \"∀ x : ℝ, 0 ≤ x → 0 ≤ x^2\" Q3/Proofs/Test.lean"
      exit 1
    fi

    NAME="$2"
    TYPE="$3"
    FILE="$4"

    echo "" >> "$FILE"
    echo "/-- TDD: TODO - prove this -/" >> "$FILE"
    echo "theorem $NAME : $TYPE := by" >> "$FILE"
    echo "  sorry" >> "$FILE"

    echo -e "${RED}RED${NC}: Added '$NAME' with sorry to $FILE"
    echo ""
    echo "Building to verify RED state..."
    lake build 2>&1 | grep -E "(sorry|$NAME)" | head -10 || true
    ;;

  #═══════════════════════════════════════════════════════════════
  # GREEN: Check if all proofs compile
  #═══════════════════════════════════════════════════════════════
  green|check)
    echo "=== TDD Status Check ==="
    echo ""

    # Build and capture output
    BUILD_OUT=$(lake build 2>&1) || true

    ERRORS=$(echo "$BUILD_OUT" | grep -c "error" || echo "0")
    SORRIES=$(echo "$BUILD_OUT" | grep -c "sorry" || echo "0")

    if [ "$ERRORS" -gt 0 ]; then
      echo -e "${RED}COMPILE ERROR${NC} - fix errors before continuing"
      echo ""
      echo "$BUILD_OUT" | grep -A2 "error" | head -20
      exit 1
    elif [ "$SORRIES" -gt 0 ]; then
      echo -e "${YELLOW}RED${NC}: $SORRIES sorry(s) remaining"
      echo ""
      echo "$BUILD_OUT" | grep "sorry"
    else
      echo -e "${GREEN}GREEN${NC}: All proofs complete!"
      echo ""
      echo "Ready for REFACTOR phase or next RED."
    fi
    ;;

  #═══════════════════════════════════════════════════════════════
  # COVERAGE: Show sorry count and axiom status
  #═══════════════════════════════════════════════════════════════
  coverage|cov)
    echo "=== TDD Coverage Report ==="
    echo ""

    echo "Sorry count by file:"
    echo "─────────────────────"
    grep -r "sorry" Q3/ --include="*.lean" 2>/dev/null | \
      grep -v "Archive" | \
      cut -d: -f1 | sort | uniq -c | sort -rn || echo "  (none found)"

    echo ""
    echo "Axiom status:"
    echo "─────────────"
    if [ -f "./scripts/check_axioms.sh" ]; then
      ./scripts/check_axioms.sh 2>/dev/null || true
    else
      lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>/dev/null || \
        echo "  (could not check axioms)"
    fi
    ;;

  #═══════════════════════════════════════════════════════════════
  # FIND: Find all sorries in codebase
  #═══════════════════════════════════════════════════════════════
  find|sorries)
    echo "=== All sorries in Q3/ ==="
    echo ""
    grep -rn "sorry" Q3/ --include="*.lean" 2>/dev/null | \
      grep -v "Archive" | \
      grep -v "-- sorry" || echo "(none found)"
    ;;

  #═══════════════════════════════════════════════════════════════
  # WATCH: Continuous build on file change
  #═══════════════════════════════════════════════════════════════
  watch)
    echo "Watching for changes... (Ctrl+C to stop)"
    echo ""

    # Use fswatch if available, otherwise polling
    if command -v fswatch &> /dev/null; then
      fswatch -o Q3/**/*.lean | while read; do
        clear
        echo "=== File changed, rebuilding... ==="
        $0 check
      done
    else
      echo "Install fswatch for better experience: brew install fswatch"
      echo "Falling back to polling every 5s..."
      while true; do
        sleep 5
        $0 check
        echo ""
        echo "(polling every 5s...)"
      done
    fi
    ;;

  #═══════════════════════════════════════════════════════════════
  # HELP
  #═══════════════════════════════════════════════════════════════
  *)
    echo "Lean 4 TDD Helper"
    echo ""
    echo "Usage: ./scripts/tdd.sh <command> [args]"
    echo ""
    echo "Commands:"
    echo "  red <name> \"<type>\" <file>  Add theorem with sorry (RED phase)"
    echo "  green, check                 Check build status (GREEN phase)"
    echo "  coverage, cov                Show sorry/axiom coverage"
    echo "  find, sorries                List all sorries"
    echo "  watch                        Continuous rebuild on change"
    echo ""
    echo "TDD Workflow:"
    echo "  1. ./scripts/tdd.sh red my_lemma \"P\" Q3/Proofs/File.lean"
    echo "  2. Edit File.lean, replace sorry with proof"
    echo "  3. ./scripts/tdd.sh check"
    echo "  4. Refactor if needed, repeat check"
    echo "  5. ./scripts/tdd.sh coverage"
    ;;
esac
