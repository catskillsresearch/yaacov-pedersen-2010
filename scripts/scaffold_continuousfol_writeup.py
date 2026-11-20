#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Generator for per-module writeup leaves of the ContinuousFOL.md tree.

Not implemented in this repository: the writeup tree (ContinuousFOL.md and the
section files ContinuousFOL/<Section>.md) is maintained by hand, and the
section module lists are kept in sync with ContinuousFOL/<Section>/*.lean.
`scripts/paper_quotes.py` imports `extract_paper_blocks` from here and is
therefore not usable either. The script exits with status 1.
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
        "scaffold_continuousfol_writeup.py: per-module writeup leaves are not\n"
        "generated in this repository; ContinuousFOL.md and the section .md\n"
        "files are maintained by hand.",
        file=sys.stderr,
    )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
