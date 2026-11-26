#!/usr/bin/env bash
# Artifact check: build, no admits, line width, CLAIMS.md and EFFORT.md
# up to date.
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
# Count characters, not bytes, whatever the locale.
long=$(python3 - <<'PY'
import glob
for f in sorted(glob.glob("theories/**/*.v", recursive=True)):
    with open(f, encoding="utf-8") as h:
        for i, line in enumerate(h, 1):
            if len(line.rstrip("\n")) > 80:
                print(f"{f}: {i}")
PY
)
if [ -n "$long" ]; then echo "$long"; exit 1; fi

echo "== nothing outside the Imp case study depends on it"
if grep -rln "LogicTransformers.ImpCube" theories --include=*.v | grep -v "^theories/ImpCube/"; then
  echo "the files above import theories/ImpCube"; exit 1
fi

echo "== CLAIMS.md matches the build"
cp CLAIMS.md /tmp/claims.committed.$$
python3 scripts/claims.py
if ! diff -q CLAIMS.md /tmp/claims.committed.$$ >/dev/null; then
  diff CLAIMS.md /tmp/claims.committed.$$ || true
  rm -f /tmp/claims.committed.$$
  echo "CLAIMS.md was out of date (now regenerated)"; exit 1
fi
rm -f /tmp/claims.committed.$$

echo "== EFFORT.md matches the sources"
python3 scripts/effort.py --check

echo "== all checks passed"
