#!/bin/bash
# Delete Feature Sandbox
# Usage: ./scripts/delete_sandbox.sh <feature-name>

FEATURE_NAME=$1
BASE_DIR=~/Documents/GitHub
MAIN_REPO=chen_q3
SANDBOX_DIR="${BASE_DIR}/${MAIN_REPO}_feature_${FEATURE_NAME}"

if [ -z "$FEATURE_NAME" ]; then
    echo "Usage: $0 <feature-name>"
    exit 1
fi

if [ ! -d "$SANDBOX_DIR" ]; then
    echo "Sandbox not found: $SANDBOX_DIR"
    exit 0
fi

echo "Deleting sandbox: $SANDBOX_DIR"
rm -rf "$SANDBOX_DIR"
echo "Done."
