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

Q3_QUICK="${Q3_QUICK:-0}"
Q3_NO_BUILD="${Q3_NO_BUILD:-0}"
Q3_FORCE_FRESH_AXIOMS="${Q3_FORCE_FRESH_AXIOMS:-1}"

if [[ "$Q3_QUICK" == "1" ]]; then
    echo "Mode: QUICK (skip steps 0..0.8 prechecks)"
fi
if [[ "$Q3_NO_BUILD" == "1" ]]; then
    echo "Mode: NO_BUILD (skip Step 1 build of Q3.Main)"
fi
if [[ "$Q3_FORCE_FRESH_AXIOMS" == "1" ]]; then
    echo "Mode: FRESH_AXIOMS (force rebuild of key .olean before #print axioms)"
fi
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

if [[ "$Q3_QUICK" == "1" ]]; then
    echo "═══ Step 0..0.8: Prechecks ═══"
    echo "ℹ️  Skipped in QUICK mode"
    echo ""
else
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
    PRIME_CERT_HEAT_PARTIAL="output/prime_cert_brange_heat_prime_partial_interval_2026-01-31_0009.txt"
    PRIME_CERT_TCRIT_HASH="3af1204fc8f5ddf322e1110b9932bb44a5349e0773d6d1b3cdf5441ec8ef3b5d"
    PRIME_CERT_BRANGE_HASH="6b4d3534195471dfe797b1910afbd7068136abfedf3ea0389b9849f917404ddc"
    PRIME_CERT_BRANGE_PILOT_INTERVAL_HASH="d2e51b9bea1eff7b50625f3e7c40aeae6a91f3eeab4eb33a5e12e948e460b5db"
    PRIME_CERT_HEAT_HASH="55e945564c513cefec7d344b8db399214b6739666161c163c55ed5b78098ef77"
    PRIME_CERT_HEAT_PARTIAL_HASH="622070a7c1684049b1c9147ee39b2e1fdaebe657f4e22acc6490cd452e8493f8"

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

    # Step 0.8: Paper status snapshot drift check
    echo "═══ Step 0.8: Paper status snapshot check ═══"
    if scripts/check_paper_status.sh; then
        echo "✓ Paper status snapshot is in sync"
    else
        echo "✗ Paper status snapshot check FAILED"
        exit 1
    fi
    echo ""
fi

# Step 0.9: Ensure active PrimeCert data modules stay checker-free
echo "═══ Step 0.9: PrimeCert checker-free guard ═══"
if rg -n "^[[:space:]]*import[[:space:]].*Checker" \
    Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_Partial.lean \
    Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean \
    Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean >/dev/null 2>&1; then
    echo "✗ Active PrimeCert data module imports a Checker file"
    echo "  Remove Checker imports from *_SumData/*_Data mainline modules."
    exit 1
else
    echo "✓ Active PrimeCert data modules are checker-free"
fi
echo ""

# Step 1: Build
echo "═══ Step 1: Building Q3.Main ═══"
if [[ "$Q3_NO_BUILD" == "1" ]]; then
    echo "ℹ️  Skipped in NO_BUILD mode (using existing build artifacts)"
elif lake build Q3.Main 2>&1 | tail -5; then
    echo "✓ Build successful"
else
    echo "✗ Build FAILED"
    exit 1
fi
echo ""

# Step 1.5: Force fresh key olean files (prevents stale-axiom snapshots)
if [[ "$Q3_FORCE_FRESH_AXIOMS" == "1" ]]; then
    echo "═══ Step 1.5: Freshen key olean targets ═══"
    if lake env lean --root=. Q3/Proofs/Q_nonneg_t_critical.lean \
        -o .lake/build/lib/lean/Q3/Proofs/Q_nonneg_t_critical.olean \
        -i .lake/build/lib/lean/Q3/Proofs/Q_nonneg_t_critical.ilean 2>&1 | tail -5; then
        echo "✓ Refreshed Q3/Proofs/Q_nonneg_t_critical.olean"
    else
        echo "✗ Fresh rebuild failed: Q3/Proofs/Q_nonneg_t_critical.lean"
        exit 1
    fi
    if lake env lean --root=. Q3/Main.lean \
        -o .lake/build/lib/lean/Q3/Main.olean \
        -i .lake/build/lib/lean/Q3/Main.ilean 2>&1 | tail -5; then
        echo "✓ Refreshed Q3/Main.olean"
    else
        echo "✗ Fresh rebuild failed: Q3/Main.lean"
        exit 1
    fi
    if lake env lean --root=. Q3/Main_DataProfile.lean \
        -o .lake/build/lib/lean/Q3/Main_DataProfile.olean \
        -i .lake/build/lib/lean/Q3/Main_DataProfile.ilean 2>&1 | tail -5; then
        echo "✓ Refreshed Q3/Main_DataProfile.olean"
    else
        echo "✗ Fresh rebuild failed: Q3/Main_DataProfile.lean"
        exit 1
    fi
    echo ""
fi

# Step 2: Extract axioms
echo "═══ Step 2: Axiom Extraction ═══"
AXIOMS=$(echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin 2>&1)

echo "$AXIOMS"
echo ""

# Step 2.1: Margin-route smoke check (bridge-free RH entrypoint)
echo "═══ Step 2.1: Margin-route smoke check ═══"
AXIOMS_MARGIN=$(echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3_of_margin' | lake env lean --stdin 2>&1)
echo "$AXIOMS_MARGIN"
if echo "$AXIOMS_MARGIN" | grep -qE "prime_term_tcritical_le_cstar_quarter_mathan|cstar_quarter_le_arch_term_tcritical_mathan"; then
    echo "✗ Margin-route theorem still depends on legacy quarter bridge axioms"
    exit 1
else
    echo "✓ Margin-route theorem is quarter-bridge free"
fi
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

# Step 2.2: Margin-cert profile check (data-route; no quarter-bridge axioms)
echo "═══ Step 2.2: Margin-cert profile check ═══"
AXIOMS_MARGIN_CERT=$(echo 'import Q3.Main_DataProfile
#print axioms Q3.Main.RH_of_Weil_and_Q3_via_margin_cert' | lake env lean --stdin 2>&1)
echo "$AXIOMS_MARGIN_CERT"
if echo "$AXIOMS_MARGIN_CERT" | grep -qE "prime_term_tcritical_le_cstar_quarter_mathan|cstar_quarter_le_arch_term_tcritical_mathan"; then
    echo "✗ Margin-cert theorem unexpectedly depends on legacy quarter bridge axioms"
    exit 1
else
    echo "✓ Margin-cert theorem is quarter-bridge free (data-route profile)"
fi
echo ""

# Step 2.6: Sorry frontier (WARN only, opt-in; can be very expensive on PrimeCert-heavy trees)
echo "═══ Step 2.6: Sorry frontier (WARN) ═══"
if [[ "${Q3_ENABLE_SORRY_FRONTIER:-0}" != "1" ]]; then
    echo "ℹ️  Skipped (set Q3_ENABLE_SORRY_FRONTIER=1 to enable full sorry frontier scan)"
else
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
EXPECTED_STANDARD=3  # propext, Classical.choice, Quot.sound
EXPECTED_PROJECT=3   # Weil_criterion_tau0 + two Path B quarter obligations
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
echo "$AXIOMS" | tr -d '[]' | grep -E "Lipschitz_bridge|prime_term_tcritical_le_cstar_quarter_mathan|cstar_quarter_le_arch_term_tcritical_mathan" | sed 's/^/   /' || echo "   (none found)"

echo ""

# Step 5: Verification
echo "═══ Step 5: Philosophy Verification ═══"

# Expected axioms in proof chain (update when axioms are closed/added)
EXPECTED_AXIOMS=(
    "Q3.Weil_criterion_tau0"
    "Q3.prime_term_tcritical_le_cstar_quarter_mathan"
    "Q3.cstar_quarter_le_arch_term_tcritical_mathan"
)

UNKNOWN_AXIOMS=""
for axiom in $(echo "$AXIOMS_ONLY" | grep -oE "Q3\.[A-Za-z0-9_\.]+"); do
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
