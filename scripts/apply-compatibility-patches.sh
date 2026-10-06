#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
dependency=.lake/packages/complexitylib
patch_file="$PWD/patches/complexitylib-asymptotics.patch"
if git -C "$dependency" apply --reverse --check "$patch_file" 2>/dev/null; then
  exit 0
fi
git -C "$dependency" apply --check "$patch_file"
git -C "$dependency" apply "$patch_file"
