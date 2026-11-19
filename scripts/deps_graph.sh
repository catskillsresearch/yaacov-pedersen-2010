#!/usr/bin/env bash
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
# Regenerate the Lean definition/theorem dependency SVG.
# Usage (from anywhere):
#   scripts/deps_graph.sh
#   scripts/deps_graph.sh /path/to/repo /path/to/out.svg
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$ROOT/scripts/lean_deps_graph.py" "$@"
