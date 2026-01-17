#!/bin/bash
# Feature Sandbox Creator
# Usage: ./scripts/create_sandbox.sh <feature-name>

set -e

FEATURE_NAME=$1
BASE_DIR=~/Documents/GitHub
MAIN_REPO=chen_q3

if [ -z "$FEATURE_NAME" ]; then
    echo "Usage: $0 <feature-name>"
    echo ""
    echo "Examples:"
    echo "  $0 P_A_continuous"
    echo "  $0 Q_nonneg"
    echo "  $0 arch_prime"
    echo ""
    echo "This will:"
    echo "  1. Clone chen_q3 to chen_q3_feature_<name>"
    echo "  2. Create feature branch"
    echo "  3. Build lake (takes ~5 min)"
    exit 1
fi

SANDBOX_DIR="${BASE_DIR}/${MAIN_REPO}_feature_${FEATURE_NAME}"

if [ -d "$SANDBOX_DIR" ]; then
    echo "ERROR: Sandbox already exists: $SANDBOX_DIR"
    echo "Delete it first: rm -rf $SANDBOX_DIR"
    exit 1
fi

echo "═══════════════════════════════════════════════════════"
echo "Creating Feature Sandbox: $FEATURE_NAME"
echo "═══════════════════════════════════════════════════════"

echo ""
echo "Step 1/3: Cloning repository..."
git clone "${BASE_DIR}/${MAIN_REPO}" "$SANDBOX_DIR"

cd "$SANDBOX_DIR"
echo ""
echo "Step 2/3: Creating feature branch..."
git checkout -b "feature/${FEATURE_NAME}"

echo ""
echo "Step 3/3: Building lake (this takes a while)..."
cd full/q3.lean.aristotle
lake build Q3.Main

echo ""
echo "═══════════════════════════════════════════════════════"
echo "SANDBOX READY"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Directory: $SANDBOX_DIR"
echo "Branch:    feature/${FEATURE_NAME}"
echo ""
echo "To start agent in NEW TERMINAL:"
echo "  cd $SANDBOX_DIR/full/q3.lean.aristotle"
echo "  claude"
echo ""
echo "When done:"
echo "  ./scripts/merge_sandbox.sh $FEATURE_NAME"
echo "═══════════════════════════════════════════════════════"
