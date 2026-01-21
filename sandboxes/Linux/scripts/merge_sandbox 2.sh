#!/bin/bash
# Merge Feature Sandbox
# Usage: ./scripts/merge_sandbox.sh <feature-name>

set -e

FEATURE_NAME=$1
BASE_DIR=~/Documents/GitHub
MAIN_REPO=chen_q3
SANDBOX_DIR="${BASE_DIR}/${MAIN_REPO}_feature_${FEATURE_NAME}"

if [ -z "$FEATURE_NAME" ]; then
    echo "Usage: $0 <feature-name>"
    exit 1
fi

if [ ! -d "$SANDBOX_DIR" ]; then
    echo "ERROR: Sandbox not found: $SANDBOX_DIR"
    exit 1
fi

echo "═══════════════════════════════════════════════════════"
echo "Merging Feature Sandbox: $FEATURE_NAME"
echo "═══════════════════════════════════════════════════════"

cd "${BASE_DIR}/${MAIN_REPO}"

echo ""
echo "Step 1/3: Adding sandbox as remote..."
git remote add "sandbox_${FEATURE_NAME}" "$SANDBOX_DIR" 2>/dev/null || true
git fetch "sandbox_${FEATURE_NAME}"

echo ""
echo "Step 2/3: Merging..."
git merge "sandbox_${FEATURE_NAME}/feature/${FEATURE_NAME}" -m "Merge feature/${FEATURE_NAME} from sandbox"

echo ""
echo "Step 3/3: Cleaning up remote..."
git remote remove "sandbox_${FEATURE_NAME}"

echo ""
echo "═══════════════════════════════════════════════════════"
echo "MERGED SUCCESSFULLY"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Sandbox still exists at: $SANDBOX_DIR"
echo "Delete with: rm -rf $SANDBOX_DIR"
echo "═══════════════════════════════════════════════════════"
