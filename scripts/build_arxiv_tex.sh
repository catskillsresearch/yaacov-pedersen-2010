#!/usr/bin/env bash
# Regenerate arxiv_with_code.md and build arxiv.tex (gitignored build artifacts).
set -euo pipefail
cd "$(dirname "$0")/.."

echo "==> Flattening ContinuousFOL.md note tree (inline Lean) -> arxiv_with_code.md"
python3 scripts/compile_md_tree.py --md-only --lean=inline
cp -f arxiv.md arxiv_with_code.md

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py
