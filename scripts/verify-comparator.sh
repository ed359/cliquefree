#!/usr/bin/env bash
# Check the statement pair with the tools bundled in the pinned Lean release.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
project_root="$repository_root/lean"

if [ "$(uname -s)" != Linux ]; then
  echo "error: the sandboxed Comparator check requires Linux and bubblewrap" >&2
  exit 1
fi

for required_command in git lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done
sandbox_binary=$(command -v "${COMPARATOR_BWRAP:-bwrap}") || {
  echo "error: install bubblewrap 0.12.0 or newer, or set COMPARATOR_BWRAP" >&2
  exit 1
}
python3 - "$sandbox_binary" "$project_root/comparator.json" <<'PYTHON'
import json
from pathlib import Path
import re
import subprocess
import sys

version = subprocess.check_output([sys.argv[1], "--version"], text=True).strip()
match = re.search(r"(\d+)\.(\d+)\.(\d+)", version)
if match is None or tuple(map(int, match.groups())) < (0, 12, 0):
    raise SystemExit("error: bubblewrap 0.12.0 or newer is required")
config = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
if config.get("enable_nanoda") is not True:
    raise SystemExit("error: comparator.json must enable the NanoDa replay")
print("Using " + version)
PYTHON

cd "$project_root"
# Use the actual toolchain binaries inside bubblewrap, rather than Elan shims.
project_lake=$(lake env which lake)
project_bin_dir=$(dirname "$project_lake")
for executable in lake leanexport leanchecker nanoda_bin; do
  if [ ! -x "$project_bin_dir/$executable" ]; then
    echo "error: pinned Lean toolchain is missing $executable" >&2
    exit 1
  fi
done
export PATH="$project_bin_dir:$PATH"
export COMPARATOR_BWRAP="$sandbox_binary"

"$project_lake" exe cache get
comparator_log=$(mktemp)
trap 'rm -f "$comparator_log"' EXIT
set +e
"$project_lake" comparator --config comparator.json 2>&1 | tee "$comparator_log"
comparator_status=${PIPESTATUS[0]}
set -e

if [ "$comparator_status" -ne 0 ]; then
  echo "error: Comparator exited with status $comparator_status" >&2
  exit "$comparator_status"
fi
if [ "$(tail -n 1 "$comparator_log")" != "Your solution is okay!" ]; then
  echo "error: Comparator did not print its exact success marker" >&2
  exit 1
fi
