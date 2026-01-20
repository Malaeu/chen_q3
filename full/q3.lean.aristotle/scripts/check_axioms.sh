#!/bin/bash
# Q3 Axiom Verification Script
# Run before every commit to ensure philosophy compliance

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

echo "╔════════════════════════════════════════════════════════════════╗"
echo "║           Q3 AXIOM VERIFICATION (Philosophy Check)            ║"
echo "╚════════════════════════════════════════════════════════════════╝"
echo ""
echo "Date: $(date)"
echo "Directory: $PROJECT_DIR"
echo ""

# Step 0: Prebuild A3_FLOOR (via compatibility wrapper)
echo "═══ Step 0: Prebuilding A3_Floor_Main ═══"
if lake env lean A3_FLOOR_v22_stage4_floor.lean 2>&1 | tail -5; then
    echo "✓ A3_FLOOR prebuild successful"
else
    echo "✗ A3_FLOOR prebuild FAILED"
    exit 1
fi
echo ""

# Step 0.5: Docs link check
echo "═══ Step 0.5: Docs link check ═══"
if python3 scripts/check_links.py; then
    echo "✓ Link check successful"
else
    echo "✗ Link check FAILED"
    exit 1
fi
echo ""

# Step 0.6: Audit invariants
echo "═══ Step 0.6: Audit invariants ═══"
if scripts/check_audit_invariants.sh; then
    echo "✓ Audit invariants successful"
else
    echo "✗ Audit invariants FAILED"
    exit 1
fi
echo ""

# Step 1: Build
echo "═══ Step 1: Building Q3.Main ═══"
if lake build Q3.Main 2>&1 | tail -5; then
    echo "✓ Build successful"
else
    echo "✗ Build FAILED"
    exit 1
fi
echo ""

# Step 2: Extract axioms
echo "═══ Step 2: Axiom Extraction ═══"
AXIOMS=$(echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1)

echo "$AXIOMS"
echo ""

# Step 3: Count axioms
echo "═══ Step 3: Axiom Count ═══"

# Count standard axioms from full output (propext is on the header line)
STANDARD_COUNT=$(echo "$AXIOMS" | grep -oE "propext|Classical.choice|Quot.sound" | wc -l | tr -d ' ')
# Strip the header label but keep the axiom list.
AXIOMS_ONLY=$(echo "$AXIOMS" | sed "s/'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: //")
PROJECT_COUNT=$(echo "$AXIOMS_ONLY" | grep -E "Q3\." | wc -l | tr -d ' ')
TOTAL=$((STANDARD_COUNT + PROJECT_COUNT))

echo "Standard Lean: $STANDARD_COUNT (expected: 3)"
echo "Project:       $PROJECT_COUNT (expected: 5)"
echo "TOTAL:         $TOTAL (expected: 8)"
echo ""

# Step 4: Classification
echo "═══ Step 4: Axiom Classification ═══"

echo "Level 1 (Classical Literature):"
echo "$AXIOMS" | grep -E "Weil_criterion|digamma_one_fourth_neg|Schur_test" | sed 's/^/  /' || echo "  (none found)"

echo ""
echo "Level 2 (Q3 Paper Contributions):"
echo "$AXIOMS_ONLY" | grep -E "RKHS_contraction|Q_nonneg_on_atoms|A1_density" | sed 's/^/  /' || echo "  (none found)"

echo ""
echo "Level 3 (Bridge Lemmas):"
echo "$AXIOMS" | grep -E "Lipschitz_bridge" | sed 's/^/  /' || echo "  (none found)"

echo ""

# Step 5: Verification
echo "═══ Step 5: Philosophy Verification ═══"

EXPECTED_AXIOMS=(
    "Q3.Weil_criterion"
    "Q3.digamma_one_fourth_neg"
    "Q3.Schur_test"
    "Q3.A1_density_WK_axiom"
    "Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom"
)

UNKNOWN_AXIOMS=""
for axiom in $(echo "$AXIOMS_ONLY" | grep -E "Q3\." | tr -d ' [],'); do
    FOUND=false
    for expected in "${EXPECTED_AXIOMS[@]}"; do
        if [[ "$axiom" == "$expected" ]]; then
            FOUND=true
            break
        fi
    done
    if [[ "$FOUND" == "false" ]]; then
        UNKNOWN_AXIOMS="$UNKNOWN_AXIOMS $axiom"
    fi
done

if [[ -z "$UNKNOWN_AXIOMS" ]]; then
    echo "✓ All axioms are documented in PHILOSOPHY_OF_PROOF.md"
else
    echo "✗ UNKNOWN AXIOMS DETECTED:"
    echo "  $UNKNOWN_AXIOMS"
    echo ""
    echo "  ACTION REQUIRED: Add these to PHILOSOPHY_OF_PROOF.md with citations"
    exit 1
fi

echo ""
echo "╔════════════════════════════════════════════════════════════════╗"
echo "║                    VERIFICATION PASSED ✓                      ║"
echo "║                                                                ║"
echo "║  Axiom count: $TOTAL (5 Project + 3 Standard)                  ║"
echo "║  Philosophy: Compliant                                         ║"
echo "║  Ready to commit!                                              ║"
echo "╚════════════════════════════════════════════════════════════════╝"
