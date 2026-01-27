#!/bin/bash
# Update Q3 API documentation
# Usage: ./scripts/update_docs.sh
#
# This script:
# 1. Rebuilds doc-gen4 documentation
# 2. Copies only Q3 docs to docs/api/ (standalone, ~1.6MB)
# 3. Cleans up unnecessary .hash/.trace files
#
# After running, commit with:
#   git add docs/api && git commit -m "Update Q3 docs"

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
DOCBUILD_DIR="$PROJECT_DIR/docbuild"
API_DIR="$PROJECT_DIR/docs/api"

echo "=== Q3 Documentation Update ==="
echo ""

# Step 1: Build docs
echo "[1/3] Building documentation..."
"$SCRIPT_DIR/build_docs.sh"

# Step 2: Copy Q3 docs only
echo ""
echo "[2/3] Copying Q3 docs to docs/api/..."
mkdir -p "$API_DIR"

# Remove old Q3 docs
rm -rf "$API_DIR/Q3" "$API_DIR/Q3.html"

# Copy fresh docs
cp -r "$DOCBUILD_DIR/.lake/build/doc/Q3" "$API_DIR/"
cp "$DOCBUILD_DIR/.lake/build/doc/Q3.html" "$API_DIR/"

# Copy assets (only if changed)
cp "$DOCBUILD_DIR/.lake/build/doc/style.css" "$API_DIR/" 2>/dev/null || true
cp "$DOCBUILD_DIR/.lake/build/doc/favicon.svg" "$API_DIR/" 2>/dev/null || true
cp "$DOCBUILD_DIR/.lake/build/doc/"*.js "$API_DIR/" 2>/dev/null || true

# Step 3: Cleanup
echo "[3/3] Cleaning up .hash/.trace files..."
find "$API_DIR" -name "*.hash" -delete
find "$API_DIR" -name "*.trace" -delete

# Optional: external literature scan (set EXTERNAL_LOOP=1)
if [ "${EXTERNAL_LOOP:-0}" = "1" ]; then
  echo ""
  echo "[ext] Running external literature loop..."
  python3 "$SCRIPT_DIR/proof_compiler/external_loop.py" --query "toeplitz a3 bridge" --query "rkhs prime cap" --max 3 || true
fi

# Summary
HTML_COUNT=$(find "$API_DIR" -name "*.html" | wc -l)
SIZE=$(du -sh "$API_DIR" | cut -f1)

echo ""
echo "=== Done ==="
echo "Location: $API_DIR"
echo "HTML files: $HTML_COUNT"
echo "Total size: $SIZE"
echo ""
echo "Next steps:"
echo "  git add docs/api"
echo "  git commit -m 'Update Q3 docs: <description>'"
echo "  git push"
