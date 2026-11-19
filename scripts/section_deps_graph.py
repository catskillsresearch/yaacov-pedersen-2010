#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build ContinuousFOL.svg: dependencies among ContinuousFOL/Section{1..9}.md.

Arrows point from a prerequisite to the section that uses it: an edge
§j → §i means some .lean listed in Section i imports a .lean listed in
Section j (i ≠ j), so results flow along the arrows. Nodes are the nine
numbered section markdown files (Ben Yaacov–Pedersen 2010).

Usage (from repo root):

    python3 scripts/section_deps_graph.py
"""

from __future__ import annotations

import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WRITEUP = ROOT / "ContinuousFOL"
LEAN_DIR = ROOT / "ContinuousFOL"
OUT_DOT = ROOT / "ContinuousFOL.dot"
OUT_SVG = ROOT / "ContinuousFOL.svg"

IMPORT_RE = re.compile(
    r"^\s*(?:public\s+)?import\s+ContinuousFOL\.([A-Za-z0-9_']+)",
    re.MULTILINE,
)
MD_IMPORT_RE = re.compile(r'@import\s+"\.\./ContinuousFOL/([^"]+\.lean)"')
MD_LEAF_LINK_RE = re.compile(r"\]\(Section\d+/([^)]+)\.md\)")

SECTION_FILES = [WRITEUP / f"Section{i}.md" for i in range(1, 10)]

# Short labels for numbered section nodes (match ContinuousFOL.md TOC).
SECTION_LABELS = {
    1: "§1 Introduction",
    2: "§2 Łukasiewicz / continuous",
    3: "§3 Axioms Group 1",
    4: "§4 Black-box theorems",
    5: "§5 Language & semantics",
    6: "§6 Substitution / completions",
    7: "§7 Axioms Group 2",
    8: "§8 Essentials",
    9: "§9 Completeness",
}


def lean_stem(name: str) -> str:
    return Path(name).stem


def section_leans() -> dict[int, set[str]]:
    mapping: dict[int, set[str]] = {}
    for i, path in enumerate(SECTION_FILES, start=1):
        text = path.read_text(encoding="utf-8")
        stems = {lean_stem(m) for m in MD_IMPORT_RE.findall(text)}
        # Barrel form (scaffold_continuousfol_writeup.py): links to SectionN/Stem.md leaves.
        stems |= {lean_stem(m) for m in MD_LEAF_LINK_RE.findall(text)}
        mapping[i] = stems
    return mapping


def lean_imports(stem: str) -> set[str]:
    path = LEAN_DIR / f"{stem}.lean"
    if not path.exists():
        return set()
    text = path.read_text(encoding="utf-8")
    return set(IMPORT_RE.findall(text))


def build_edges(sec_leans: dict[int, set[str]]) -> set[tuple[int, int]]:
    stem_to_sec: dict[str, int] = {}
    for sec, stems in sec_leans.items():
        for s in stems:
            if s in stem_to_sec and stem_to_sec[s] != sec:
                raise SystemExit(f"lean {s}.lean listed in §{stem_to_sec[s]} and §{sec}")
            stem_to_sec[s] = sec

    edges: set[tuple[int, int]] = set()
    for sec, stems in sec_leans.items():
        for stem in stems:
            for dep in lean_imports(stem):
                if dep not in stem_to_sec:
                    continue
                other = stem_to_sec[dep]
                if other != sec:
                    # importer section → imported section
                    edges.add((sec, other))
    return edges


def write_dot(edges: set[tuple[int, int]]) -> str:
    lines = [
        "digraph ContinuousFOLSections {",
        "  graph [rankdir=LR, bgcolor=\"white\", pad=\"0.3\", nodesep=\"0.45\", ranksep=\"0.7\"];",
        "  node [shape=box, style=\"rounded,filled\", fillcolor=\"#dbeafe\",",
        "        color=\"#1e40af\", fontname=\"Helvetica\", fontsize=12,",
        "        fontcolor=\"#0f172a\", margin=\"0.18,0.12\"];",
        "  edge [color=\"#64748b\", arrowsize=0.7];",
        "",
    ]
    for i in range(1, 7):
        label = SECTION_LABELS[i]
        href = f"ContinuousFOL/Section{i}.md"
        lines.append(
            f'  S{i} [label="{label}", URL="{href}", tooltip="ContinuousFOL/Section{i}.md"];'
        )
    lines.append("")
    for a, b in sorted(edges):
        # a imports b: draw prerequisite b -> user a.
        lines.append(f"  S{b} -> S{a};")
    lines.append("}")
    return "\n".join(lines) + "\n"


def main() -> int:
    sec_leans = section_leans()
    for i, stems in sec_leans.items():
        print(f"§{i}: {len(stems)} lean modules")
    edges = build_edges(sec_leans)
    print(f"cross-section import edges: {len(edges)} (drawn prerequisite → user)")
    for a, b in sorted(edges, key=lambda e: (e[1], e[0])):
        print(f"  §{b} → §{a}  (§{a} imports from §{b})")

    dot = write_dot(edges)
    OUT_DOT.write_text(dot, encoding="utf-8")
    try:
        subprocess.run(
            ["dot", "-Tsvg", "-o", str(OUT_SVG), str(OUT_DOT)],
            check=True,
        )
    except FileNotFoundError:
        print("graphviz `dot` not found; wrote", OUT_DOT, file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as e:
        print("dot failed:", e, file=sys.stderr)
        return 1
    print("wrote", OUT_SVG.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
