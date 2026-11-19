#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Regenerate ContinuousFOLComparator/Challenge.lean from the proof chart.

Stub: fill in declaration extraction once paper-facing holes are inventoried
in `holes-graph.json` / `ContinuousFOL/`. Until then this script exits with
instructions rather than emitting a a paper-specific Challenge body.
"""
from __future__ import annotations

import sys


def main() -> int:
    print(
        "regen_challenge.py: not yet configured for ContinuousFOL.\n"
        "Inventorize paper-facing declarations in holes-graph.json, then wire\n"
        "Challenge/Solution extraction here (Palomar Comparator pattern).",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
