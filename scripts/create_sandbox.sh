#!/bin/bash
# Feature Sandbox Creator (with symlink-based Lake caching)
# Usage: ./scripts/create_sandbox.sh <feature-name>

set -e

FEATURE_NAME=$1
BASE_DIR=~/Documents/GitHub
MAIN_REPO=chen_q3
MAIN_DIR="${BASE_DIR}/${MAIN_REPO}"
LEAN_SUBDIR="full/q3.lean.aristotle"

if [ -z "$FEATURE_NAME" ]; then
    echo "Usage: $0 <feature-name>"
    echo ""
    echo "Examples:"
    echo "  $0 P_A_continuous"
    echo "  $0 Q_nonneg"
    echo "  $0 arch_prime"
    echo ""
    echo "This will:"
    echo "  1. rsync chen_q3 (without .lake) → chen_q3_feature_<name>"
    echo "  2. Symlink .lake/packages and .lake/build (saves 7.6GB!)"
    echo "  3. Create feature branch"
    echo "  4. Ready instantly (no lake build needed)"
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

# === Step 1: rsync without .lake (fast!) ===
echo ""
echo "Step 1/3: Syncing repository (without .lake)..."
rsync -a --exclude='.lake' "${MAIN_DIR}/" "$SANDBOX_DIR/"
echo "  Synced ~26MB (instead of 7.7GB with .lake)"

# === Step 2: Symlink Lake cache ===
echo ""
echo "Step 2/3: Creating Lake symlinks..."
MAIN_LAKE="${MAIN_DIR}/${LEAN_SUBDIR}/.lake"
SANDBOX_LAKE="${SANDBOX_DIR}/${LEAN_SUBDIR}/.lake"

mkdir -p "$SANDBOX_LAKE"

if [ -d "${MAIN_LAKE}/packages" ]; then
    ln -sf "${MAIN_LAKE}/packages" "${SANDBOX_LAKE}/packages"
    echo "  packages -> ${MAIN_LAKE}/packages (7.6GB shared)"
fi

if [ -d "${MAIN_LAKE}/build" ]; then
    ln -sf "${MAIN_LAKE}/build" "${SANDBOX_LAKE}/build"
    echo "  build -> ${MAIN_LAKE}/build (82MB shared)"
fi

# === Step 3: Create feature branch ===
echo ""
echo "Step 3/3: Creating feature branch..."
cd "$SANDBOX_DIR"
git checkout -b "feature/${FEATURE_NAME}"

# === Done! ===
echo ""
echo "═══════════════════════════════════════════════════════"
echo "SANDBOX READY (instant - no lake build needed!)"
echo "═══════════════════════════════════════════════════════"
echo ""
echo "Directory: $SANDBOX_DIR"
echo "Branch:    feature/${FEATURE_NAME}"
echo "Storage:   ~26MB (symlinks to shared 7.7GB cache)"
echo ""
echo "To start agent in NEW TERMINAL:"
echo "  cd $SANDBOX_DIR/full/q3.lean.aristotle"
echo "  claude"
echo ""
echo "Or use: bx $FEATURE_NAME"
echo ""
echo "When done:"
echo "  ./scripts/merge_sandbox.sh $FEATURE_NAME"
echo "═══════════════════════════════════════════════════════"
