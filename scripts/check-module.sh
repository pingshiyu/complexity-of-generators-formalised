#!/usr/bin/env bash
# Check one source and refresh its local interface. Build its dependencies first.
set -euo pipefail
# Keep parallel leaf checks from exhausting the shared compiler worker pool.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-1}"
project_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_root"
module=${1%.lean}
mkdir -p ".lake/build/lib/lean/$(dirname -- "$module")"
exec "${LAKE:-lake}" env lean -j "$LEAN_NUM_THREADS" -DautoImplicit=false \
  -o ".lake/build/lib/lean/$module.olean" "$module.lean"
