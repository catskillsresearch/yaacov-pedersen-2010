#!/usr/bin/env bash
# Flatten ContinuousFOL.md → arxiv.md → arxiv.tex → ContinuousFOL.pdf (Lean-highlighted).
set -euo pipefail
cd "$(dirname "$0")/.."

TEX="arxiv.tex"
PDF="arxiv.pdf"
OUT="ContinuousFOL.pdf"

echo "==> Flattening ContinuousFOL.md note tree (inline Lean)"
python3 scripts/compile_md_tree.py --md-only --lean=inline

echo "==> Preparing arxiv_with_code.md"
cp -f arxiv.md arxiv_with_code.md

echo "==> Building arxiv.tex + lean-listings/ + figures/"
python3 scripts/build_arxiv_tex.py

echo "==> Compiling PDF (pdfLaTeX + BibTeX via latexmk)"
command -v bibtex >/dev/null || { echo "BibTeX is required" >&2; exit 1; }
test -s references.bib || { echo "Missing references.bib" >&2; exit 1; }
latexmk -C "$TEX" >/dev/null 2>&1 || true
rm -f arxiv.aux arxiv.out arxiv.toc arxiv.bbl arxiv.blg
latexmk -pdf -bibtex \
  -pdflatex="pdflatex -interaction=nonstopmode -halt-on-error" \
  -interaction=nonstopmode \
  -halt-on-error \
  "$TEX" || {
  echo "latexmk reported errors; tail of log:" >&2
  tail -n 60 arxiv.log >&2 || true
  exit 1
}

test -s arxiv.bbl || { echo "BibTeX produced no bibliography" >&2; exit 1; }
if grep -Eq 'Citation .* undefined|There were undefined citations|There were undefined references' arxiv.log; then
  echo "Unresolved references/citations: see arxiv.log" >&2
  exit 1
fi

echo "wrote $PDF ($(du -h "$PDF" | cut -f1))"
cp -f "$PDF" "$OUT"
cp -f "$PDF" view.pdf
echo "wrote $OUT and view.pdf"
