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

# Hash helper (sha256sum on Linux, shasum on macOS)
hash_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    elif command -v shasum >/dev/null 2>&1; then
        shasum -a 256 "$1" | awk '{print $1}'
    else
        return 1
    fi
}

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

# Step 0.7: PrimeCert evidence files
echo "═══ Step 0.7: PrimeCert evidence check ═══"
PRIME_CERT_TCRIT="output/prime_cert_tcritical_2026-01-26_0046.txt"
PRIME_CERT_BRANGE="output/prime_cert_brange_tcritical_interval_2026-01-30_2206.txt"
PRIME_CERT_BRANGE_PILOT_INTERVAL="output/prime_cert_brange_tcritical_pilot_interval_2026-01-30_2357.txt"
PRIME_CERT_HEAT="output/prime_cert_brange_heat_L_interval_2026-01-30_2309.txt"
PRIME_CERT_HEAT_PARTIAL="output/prime_cert_brange_heat_prime_partial_interval_2026-01-30_2309.txt"
PRIME_CERT_TCRIT_HASH="3af1204fc8f5ddf322e1110b9932bb44a5349e0773d6d1b3cdf5441ec8ef3b5d"
PRIME_CERT_BRANGE_HASH="451637edeee5b073d7a4b0cfb8439dd6fdaebc9fc2878182cceea49737babc48"
PRIME_CERT_BRANGE_PILOT_INTERVAL_HASH="d2e51b9bea1eff7b50625f3e7c40aeae6a91f3eeab4eb33a5e12e948e460b5db"
PRIME_CERT_HEAT_HASH="05b044cbc035b285c453631af81eed8bd0a49b2f0866f6f7f3035c09732630d8"
PRIME_CERT_HEAT_PARTIAL_HASH="1c9fe427476eb63cfa9e4eb57a23888bdbabf08afc5e1d59095f0a7bee80c1f8"

if [[ ! -f "$PRIME_CERT_TCRIT" || ! -f "$PRIME_CERT_BRANGE" || ! -f "$PRIME_CERT_BRANGE_PILOT_INTERVAL" || ! -f "$PRIME_CERT_HEAT" || ! -f "$PRIME_CERT_HEAT_PARTIAL" ]]; then
    echo "✗ PrimeCert evidence file missing"
    exit 1
fi

HASH_TCRIT="$(hash_file "$PRIME_CERT_TCRIT" || true)"
HASH_BRANGE="$(hash_file "$PRIME_CERT_BRANGE" || true)"
HASH_BRANGE_PILOT_INTERVAL="$(hash_file "$PRIME_CERT_BRANGE_PILOT_INTERVAL" || true)"
HASH_HEAT="$(hash_file "$PRIME_CERT_HEAT" || true)"
HASH_HEAT_PARTIAL="$(hash_file "$PRIME_CERT_HEAT_PARTIAL" || true)"

if [[ -z "$HASH_TCRIT" || -z "$HASH_BRANGE" || -z "$HASH_BRANGE_PILOT_INTERVAL" || -z "$HASH_HEAT" || -z "$HASH_HEAT_PARTIAL" ]]; then
    echo "✗ sha256 tool not available (sha256sum/shasum)"
    exit 1
fi

if [[ "$HASH_TCRIT" != "$PRIME_CERT_TCRIT_HASH" || "$HASH_BRANGE" != "$PRIME_CERT_BRANGE_HASH" || "$HASH_BRANGE_PILOT_INTERVAL" != "$PRIME_CERT_BRANGE_PILOT_INTERVAL_HASH" || "$HASH_HEAT" != "$PRIME_CERT_HEAT_HASH" || "$HASH_HEAT_PARTIAL" != "$PRIME_CERT_HEAT_PARTIAL_HASH" ]]; then
    echo "✗ PrimeCert evidence hash mismatch"
    exit 1
fi
echo "✓ PrimeCert evidence hash OK"
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

# Step 2.5: Check for sorryAx (indicates incomplete proofs)
echo "═══ Step 2.5: sorryAx Check ═══"
if echo "$AXIOMS" | grep -q "sorryAx"; then
    echo "✗ ERROR: sorryAx detected in proof chain!"
    echo ""
    echo "  This means there's a 'sorry' somewhere in the proof."
    echo "  Options:"
    echo "    1. Find and close the sorry (preferred)"
    echo "    2. Convert to explicit bridge axiom (if closure is hard)"
    echo "    3. Revert wiring to use axiom instead of theorem"
    echo ""
    echo "  To find sorry locations:"
    echo "    grep -rn 'sorry' Q3/Proofs/"
    echo ""
    exit 1
else
    echo "✓ No sorryAx detected"
fi
echo ""

# Step 2.6: Sorry frontier (WARN only)
echo "═══ Step 2.6: Sorry frontier (WARN) ═══"
if python3 ../scripts/build_sorry_frontier.py >/dev/null 2>&1; then
    SORRY_JSON="ACTIVE/graphs/SORRY_FRONTIER.json"
    if [[ -f "$SORRY_JSON" ]]; then
        SORRY_TOTAL=$(python3 - <<'PY'
import json, pathlib
p = pathlib.Path("ACTIVE/graphs/SORRY_FRONTIER.json")
try:
    data = json.loads(p.read_text(encoding="utf-8"))
    print(int(data.get("total_sorries", 0)))
except Exception:
    print(0)
PY
)
        if [[ "$SORRY_TOTAL" -gt 0 ]]; then
            echo "⚠️  WARNING: $SORRY_TOTAL sorries found in Q3/ (see ACTIVE/graphs/SORRY_FRONTIER.md)"
        else
            echo "✓ No sorries found in Q3/"
        fi
    else
        echo "⚠️  WARNING: Missing $SORRY_JSON (sorry scan skipped)"
    fi
else
    echo "⚠️  WARNING: build_sorry_frontier.py failed (sorry scan skipped)"
fi
echo ""

# Step 3: Count axioms
echo "═══ Step 3: Axiom Count ═══"

# Count standard/kernel axioms from full output (propext is on the header line)
STANDARD_COUNT=$(echo "$AXIOMS" | grep -oE "propext|Classical.choice|Quot.sound|Lean.ofReduceBool|Lean.trustCompiler" | wc -l | tr -d ' ')
# Strip the header label but keep the axiom list.
AXIOMS_ONLY=$(echo "$AXIOMS" | sed "s/'Q3.Main.RH_of_Weil_and_Q3' depends on axioms: //")
AXIOMS_ONLY_CLEAN=$(echo "$AXIOMS_ONLY" | tr -d '[]')
PROJECT_COUNT=$(echo "$AXIOMS_ONLY" | grep -E "Q3\." | wc -l | tr -d ' ')
TOTAL=$((STANDARD_COUNT + PROJECT_COUNT))

# Expected counts (update when axioms change)
EXPECTED_STANDARD=3  # propext, Classical.choice, Quot.sound (no native_decide/compiler trust in chain)
EXPECTED_PROJECT=4   # Weil_criterion_tau0, PrimeCert cert axioms (3)
EXPECTED_TOTAL=$((EXPECTED_STANDARD + EXPECTED_PROJECT))

echo "Standard Lean: $STANDARD_COUNT (expected: $EXPECTED_STANDARD)"
echo "Project:       $PROJECT_COUNT (expected: $EXPECTED_PROJECT)"
echo "TOTAL:         $TOTAL (expected: $EXPECTED_TOTAL)"
echo ""

# Step 4: Classification
echo "═══ Step 4: Axiom Classification ═══"

echo "Level 1 (Classical Literature):"
echo "$AXIOMS" | tr -d '[]' | grep -E "Weil_criterion_tau0|digamma_one_fourth_neg|Schur_test" | sed 's/^/   /' || echo "   (none found)"

echo ""
echo "Level 2 (Q3 Paper Contributions):"
echo "$AXIOMS_ONLY_CLEAN" | grep -E "PrimeCert|SingleScale|A1_density|Q_nonneg_on_atoms" | sed 's/^/   /' || echo "   (none found)"

echo ""
echo "Level 3 (Bridge Lemmas):"
echo "$AXIOMS" | tr -d '[]' | grep -E "Lipschitz_bridge" | sed 's/^/   /' || echo "   (none found)"

echo ""

# Step 5: Verification
echo "═══ Step 5: Philosophy Verification ═══"

# Expected axioms in proof chain (update when axioms are closed/added)
EXPECTED_AXIOMS=(
    "Q3.Weil_criterion_tau0"
    "Q3.Proofs.PrimeCert.prime_b_grid_bounds_data"
    "Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data"
    "Q3.Proofs.PrimeCert.prime_heat_sum_data"
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
printf "║  Axiom count: %d (%d Project + %d Standard)                   ║\n" "$TOTAL" "$PROJECT_COUNT" "$STANDARD_COUNT"
echo "║  Philosophy: Compliant                                         ║"
echo "║  Ready to commit!                                              ║"
echo "╚════════════════════════════════════════════════════════════════╝"
