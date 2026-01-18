#!/bin/bash
# List all Feature Sandboxes
# Usage: ./scripts/list_sandboxes.sh

BASE_DIR=~/Documents/GitHub
MAIN_REPO=chen_q3

echo "═══════════════════════════════════════════════════════"
echo "Active Feature Sandboxes"
echo "═══════════════════════════════════════════════════════"
echo ""

count=0
total_real=0
LEAN_SUBDIR="full/q3.lean.aristotle"

for dir in "${BASE_DIR}/${MAIN_REPO}_feature_"*/; do
    if [ -d "$dir" ]; then
        name=$(basename "$dir" | sed "s/${MAIN_REPO}_feature_//")
        branch=$(cd "$dir" && git branch --show-current 2>/dev/null || echo "unknown")

        # Check symlink status
        lake_dir="${dir}${LEAN_SUBDIR}/.lake"
        if [ -L "${lake_dir}/packages" ]; then
            symlink_status="symlinked (saves 7.6GB)"
            # Real size without following symlinks
            size=$(du -sh -H "$dir" 2>/dev/null | cut -f1)
        else
            symlink_status="FULL COPY (no symlinks)"
            size=$(du -sh "$dir" 2>/dev/null | cut -f1)
        fi

        echo "  $name"
        echo "    Directory: $dir"
        echo "    Branch:    $branch"
        echo "    Size:      $size"
        echo "    Lake:      $symlink_status"
        echo ""
        count=$((count + 1))
    fi
done

if [ $count -eq 0 ]; then
    echo "  (none)"
    echo ""
fi

echo "═══════════════════════════════════════════════════════"
echo "Total: $count sandbox(es)"
echo "═══════════════════════════════════════════════════════"
