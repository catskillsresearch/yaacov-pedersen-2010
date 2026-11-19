#!/usr/bin/env bash
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Vision OCR pipeline wrapper (see scripts/ocr_pdf_pipeline.py).
# Default PDF: sources/yaacov_pedersen_2010.pdf
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
if [[ ! -x .venv-ocr/bin/python ]]; then
  python3 -m venv .venv-ocr
  .venv-ocr/bin/pip install -r scripts/requirements-ocr.txt
fi
# If the first argument is a flag (or missing), default to Yaacov–Pedersen PDF.
if [[ $# -eq 0 ]] || [[ "${1:-}" == -* ]]; then
  echo "ocr_pdf_pipeline: no PDF given; defaulting to sources/yaacov_pedersen_2010.pdf" >&2
  set -- sources/yaacov_pedersen_2010.pdf "$@"
fi
exec .venv-ocr/bin/python scripts/ocr_pdf_pipeline.py "$@"
