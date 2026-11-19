#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Scaffold / refresh the ContinuousFOL.md writeup tree from ContinuousFOL/*.lean.

Stub: wire leaf generation (aisummary / math / ailean sidecars, section SVGs,
gist sync) once the Lean library has paper-facing modules. Until then this
exits with instructions.
"""
from __future__ import annotations

import argparse
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--restamp", metavar="MODULE")
    parser.parse_args()
    print(
        "scaffold_continuousfol_writeup.py: not yet configured.\n"
        "Add ContinuousFOL/*.lean modules with Paper: ascriptions, then port\n"
        "the writeup scaffolder against ContinuousFOL.md / ContinuousFOL/.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
