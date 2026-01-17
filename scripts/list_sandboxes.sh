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
for dir in "${BASE_DIR}/${MAIN_REPO}_feature_"*/; do
    if [ -d "$dir" ]; then
        name=$(basename "$dir" | sed "s/${MAIN_REPO}_feature_//")
        branch=$(cd "$dir" && git branch --show-current 2>/dev/null || echo "unknown")
        size=$(du -sh "$dir" 2>/dev/null | cut -f1)
        echo "  $name"
        echo "    Directory: $dir"
        echo "    Branch:    $branch"
        echo "    Size:      $size"
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
