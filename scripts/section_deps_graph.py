#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build ContinuousFOL.svg: dependencies among ContinuousFOL/Section{1..9}.md.

Arrows point from a prerequisite to the section that uses it: an edge
§j → §i means some .lean listed in Section i imports a .lean listed in
Section j (i ≠ j), so results flow along the arrows. Edges implied by
longer paths are omitted (transitive reduction). Nodes are the nine
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
    r"^\s*(?:public\s+)?import\s+(ContinuousFOL(?:\.[A-Za-z0-9_']+)+)",
    re.MULTILINE,
)
MD_LEAF_LINK_RE = re.compile(r"\]\((Section\d+/[^)]+\.md)\)")
LEAF_LEAN_RE = re.compile(r'@import\s+"(?:\.\./)+(ContinuousFOL/[^"]+\.lean)"')

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


def module_of(rel: str) -> str:
    """`ContinuousFOL/A/B.lean` -> `ContinuousFOL.A.B`."""
    return rel[: -len(".lean")].replace("/", ".")


def section_leans() -> dict[int, set[str]]:
    """Section number -> Lean module names, read from the barrel's leaf pages."""
    mapping: dict[int, set[str]] = {}
    for i, path in enumerate(SECTION_FILES, start=1):
        text = path.read_text(encoding="utf-8")
        mods: set[str] = set()
        for leaf in MD_LEAF_LINK_RE.findall(text):
            leaf_text = (WRITEUP / leaf).read_text(encoding="utf-8")
            mods |= {module_of(m) for m in LEAF_LEAN_RE.findall(leaf_text)}
        mapping[i] = mods
    return mapping


def lean_imports(module: str) -> set[str]:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.exists():
        return set()
    return set(IMPORT_RE.findall(path.read_text(encoding="utf-8")))


def build_edges(sec_leans: dict[int, set[str]]) -> set[tuple[int, int]]:
    mod_to_sec: dict[str, int] = {}
    for sec, mods in sec_leans.items():
        for m in mods:
            if m in mod_to_sec and mod_to_sec[m] != sec:
                raise SystemExit(f"{m} listed in §{mod_to_sec[m]} and §{sec}")
            mod_to_sec[m] = sec

    edges: set[tuple[int, int]] = set()
    for sec, mods in sec_leans.items():
        for m in mods:
            for dep in lean_imports(m):
                other = mod_to_sec.get(dep)
                if other is not None and other != sec:
                    # importer section -> imported section
                    edges.add((sec, other))
    return edges


def transitive_reduction(edges: set[tuple[int, int]]) -> set[tuple[int, int]]:
    """Drop an edge a->b when b is reachable from a by a longer path."""
    succ: dict[int, set[int]] = defaultdict(set)
    for a, b in edges:
        succ[a].add(b)

    def reach(start: int, skip: tuple[int, int]) -> set[int]:
        seen: set[int] = set()
        stack = [start]
        while stack:
            x = stack.pop()
            for y in succ[x]:
                if (x, y) == skip or y in seen:
                    continue
                seen.add(y)
                stack.append(y)
        return seen

    return {e for e in edges if e[1] not in reach(e[0], e)}


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
    for i in range(1, 10):
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
    all_edges = build_edges(sec_leans)
    edges = transitive_reduction(all_edges)
    print(
        f"cross-section import edges: {len(all_edges)} "
        f"({len(edges)} after transitive reduction; drawn prerequisite → user)"
    )
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
