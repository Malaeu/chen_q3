#!/bin/bash
# Build Q3 documentation with doc-gen4
# Usage: ./scripts/build_docs.sh

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
DOCBUILD_DIR="$PROJECT_DIR/docbuild"

# Detect Lean toolchain
# lean-toolchain format: leanprover/lean4:v4.24.0
# elan folder format:    leanprover--lean4---v4.24.0
LEAN_VERSION=$(cat "$PROJECT_DIR/lean-toolchain" | tr -d '[:space:]')
TOOLCHAIN_FOLDER=$(echo "$LEAN_VERSION" | sed 's|/|--|g' | sed 's|:|---|g')
TOOLCHAIN_PATH="$HOME/.elan/toolchains/$TOOLCHAIN_FOLDER"

if [[ ! -d "$TOOLCHAIN_PATH" ]]; then
    echo "Error: Toolchain not found at $TOOLCHAIN_PATH"
    echo "Run: elan toolchain install $LEAN_VERSION"
    exit 1
fi

echo "=== Q3 Documentation Build ==="
echo "Project: $PROJECT_DIR"
echo "Toolchain: $LEAN_VERSION"
echo ""

# Set LD_LIBRARY_PATH for doc-gen4
export LD_LIBRARY_PATH="$TOOLCHAIN_PATH/lib:$LD_LIBRARY_PATH"

cd "$DOCBUILD_DIR"

echo "Building documentation..."
lake build Q3:docs 2>&1 | tee docbuild.log

echo ""
echo "=== Build Complete ==="
echo "Documentation: $DOCBUILD_DIR/.lake/build/doc/"
echo "Open: $DOCBUILD_DIR/.lake/build/doc/Q3.html"
echo ""
echo "To serve locally:"
echo "  cd $DOCBUILD_DIR/.lake/build/doc && python3 -m http.server 8000"
