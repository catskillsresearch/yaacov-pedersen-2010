#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build holes-graph.json and HOLES.md for the ContinuousFOL proof-hole board.

Scans ContinuousFOL/**/*.lean for paper-facing theorems/lemmas once NODES is
populated. Until then, writes an empty-but-valid board skeleton.
"""
from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "ContinuousFOL"
OUT_JSON = ROOT / "holes-graph.json"
OUT_HTML = ROOT / "holes.html"
HTML_EMBED_MARKER = "/*HOLES_GRAPH_JSON*/"
OUT_MD = ROOT / "HOLES.md"
OUT_EDGES = ROOT / "holes-edges.txt"

SORRY_RE = re.compile(r"(?<![\w-])sorry(?![\w-])")
DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z0-9_']+)")

# Paper-facing nodes (id → metadata). Fill as sections are formalized.
# Section numbers follow Ben Yaacov–Pedersen 2010.
NODES: dict[str, dict] = {
    # Example seed (remove once real chart nodes exist):
    # "completeness": {
    #     "label": "§9 Completeness",
    #     "section": 9,
    #     "file": "ContinuousFOL/Completeness.lean",
    #     "detail": "Consistent ⇒ completely satisfiable.",
    # },
}

# Hard dependency edges B→A: proof of A needs B.
EDGES: list[tuple[str, str]] = []


def main() -> None:
    now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    nodes = []
    for nid, meta in NODES.items():
        status = "open"
        lean = ROOT / meta["file"]
        if lean.is_file():
            text = lean.read_text(encoding="utf-8")
            # Rough: done if the named decl exists and has no bare sorry in file.
            # Refined scanning lands with the first real chart inventory.
            if not SORRY_RE.search(text) and DECL_RE.search(text, re.M):
                status = "done"
        nodes.append(
            {
                "id": nid,
                "label": meta["label"],
                "section": meta["section"],
                "file": meta["file"],
                "status": status,
                "blocker": None,
                "detail": meta.get("detail", ""),
            }
        )
    graph = {
        "updated": now,
        "sorryCount": sum(1 for n in nodes if n["status"] != "done"),
        "legend": {
            "open": "No unfinished required proof-deps — try next",
            "blocked": "Waiting on incomplete required proof-deps",
            "done": "Proved (no sorry)",
        },
        "notes": [
            "Hard edge B→A: Lean proof of A still needs B.",
            "Regenerate with: python3 scripts/build_holes.py",
            "Writeup root: ContinuousFOL.md (not a topic nickname from another paper).",
        ],
        "nodes": nodes,
        "edges": [{"from": a, "to": b, "kind": "hard"} for a, b in EDGES],
    }
    OUT_JSON.write_text(json.dumps(graph, indent=2) + "\n", encoding="utf-8")
    OUT_EDGES.write_text(
        "\n".join(f"{a} -> {b}" for a, b in EDGES) + ("\n" if EDGES else ""),
        encoding="utf-8",
    )

    open_n = sum(1 for n in nodes if n["status"] == "open")
    done_n = sum(1 for n in nodes if n["status"] == "done")
    md = [
        "# Proof holes (ContinuousFOL / Ben Yaacov–Pedersen 2010)",
        "",
        "Inventory of paper-facing Lean holes, ordered **prove-first**.",
        "",
        f"**Updated:** {now}",
        f"**Holes:** {open_n} open · {done_n} done · {len(nodes)} chart nodes.",
        "",
        "**Live board:** [`holes.html`](holes.html) (when embedded).",
        "",
        "**Writeup:** [`ContinuousFOL.md`](ContinuousFOL.md).",
        "",
        "```bash",
        "python3 scripts/build_holes.py",
        "```",
        "",
        "## Open now",
        "",
    ]
    opens = [n for n in nodes if n["status"] == "open"]
    if not opens:
        md.append("_No chart nodes yet — add entries to `NODES` in `scripts/build_holes.py`._")
    else:
        md.append("| Status | Id | Label | File |")
        md.append("|---|---|---|---|")
        for n in opens:
            md.append(f"| {n['status']} | `{n['id']}` | {n['label']} | `{n['file']}` |")
    md.append("")
    OUT_MD.write_text("\n".join(md) + "\n", encoding="utf-8")

    # Minimal HTML board if missing; else refresh embedded JSON marker.
    if OUT_HTML.is_file():
        html = OUT_HTML.read_text(encoding="utf-8")
        if HTML_EMBED_MARKER in html:
            # Replace JSON after marker until next script close — keep simple embed.
            pass
    else:
        OUT_HTML.write_text(
            "<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">"
            "<title>ContinuousFOL holes</title></head><body>"
            "<h1>ContinuousFOL proof holes</h1>"
            "<p>Open <code>HOLES.md</code>; full interactive board lands with the chart.</p>"
            f"<script>const HOLES_GRAPH = {json.dumps(graph)};"
            f"{HTML_EMBED_MARKER}</script>"
            "</body></html>\n",
            encoding="utf-8",
        )
    print(f"wrote {OUT_JSON.relative_to(ROOT)} ({len(nodes)} nodes)")
    print(f"wrote {OUT_MD.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
