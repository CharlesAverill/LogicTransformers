#!/usr/bin/env bash
# Artifact check: build, no admits, line width, and CLAIMS.md up to date.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== dune build"
dune build 2>&1 | grep -v "^    " || true
dune build

echo "== no Admitted or admit"
if grep -rn "Admitted\|admit\." theories; then
  echo "found admits"; exit 1
fi

echo "== no line over 80 characters"
long=$(awk 'length > 80 {print FILENAME": "FNR}' $(find theories -name '*.v'))
if [ -n "$long" ]; then echo "$long"; exit 1; fi

echo "== CLAIMS.md matches the build"
cp CLAIMS.md /tmp/claims.committed.$$
python3 scripts/claims.py
if ! diff -q CLAIMS.md /tmp/claims.committed.$$ >/dev/null; then
  diff CLAIMS.md /tmp/claims.committed.$$ || true
  rm -f /tmp/claims.committed.$$
  echo "CLAIMS.md was out of date (now regenerated)"; exit 1
fi
rm -f /tmp/claims.committed.$$

echo "== all checks passed"
