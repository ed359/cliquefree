#!/usr/bin/env bash
# Build once, retaining doc-gen4's database, traces and rendered pages between runs.
set -euo pipefail
cd "$(dirname "$0")/.."

# Use doc-gen4's interproject linking mode (PR #396). Architect's small helper
# library is local because it is not included in Mathlib's published docs.
export DOCGEN_LOCAL_MODULE_ROOTS=Cliquefree,Architect
export DOCGEN_DEPS_DOCS_URL=https://leanprover-community.github.io/mathlib4_docs
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

mkdir -p docbuild/docs
cp scripts/docgen/lakefile.toml docbuild/lakefile.toml
cp lean/lean-toolchain docbuild/lean-toolchain
# Supply the empty bibliography expected by doc-gen4.
touch docbuild/docs/references.bib
(
  cd docbuild
  MATHLIB_NO_CACHE_ON_UPDATE=1 lake update cliquefree doc-gen4
)

# A generator upgrade must not silently substitute different proof dependencies.
python3 - <<'PY'
import json
from pathlib import Path

def revisions(path):
    return {p["name"]: (p["url"], p["rev"])
            for p in json.loads(Path(path).read_text())["packages"]
            if p["type"] == "git"}

expected = revisions("lean/lake-manifest.json")
actual = revisions("docbuild/lake-manifest.json")
changed = [name for name, rev in expected.items() if actual.get(name) != rev]
if changed:
    raise SystemExit("doc-gen4 changed proof dependency pins: " + ", ".join(changed))
PY

python3 scripts/prune-api-docs.py
(
  cd docbuild
  lake build Cliquefree:docs
)
