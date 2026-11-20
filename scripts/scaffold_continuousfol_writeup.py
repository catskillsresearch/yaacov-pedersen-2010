#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Scaffold the ContinuousFOL writeup tree: one Markdown leaf per Lean module.

Layout (all under ``ContinuousFOL/``, next to the Lean library)::

  ContinuousFOL.md                         root: title + chapter list
  ContinuousFOL/Abstract.md, Introduction.md
  ContinuousFOL/Section{N}.md              section barrel (blurb, notes, SVG, leaf list)
  ContinuousFOL/Section{N}.svg / .dot      import graph between the section's modules
  ContinuousFOL/Section{N}/{Leaf}.md       one leaf per Lean module, importing
      {Leaf}_math.txt      green boxes: the paper passages the module formalizes,
                           paraphrased in our own mathematical English
      {Leaf}_aisummary.txt short summary of the module
      {Leaf}_ailean.txt    the module's definitions, theorems and proofs in
                           mathematical English, written from the Lean code
      the full Lean source (``@import "../../ContinuousFOL/....lean"``)

The prose lives in ``ContinuousFOL/module_writeup.json`` (one entry per module,
keyed by the module path relative to ``ContinuousFOL/``).  Each entry records the
SHA-256 of the Lean file it was written from; ``--check`` fails when an entry is
missing or the Lean file changed since (STALE), so the prose gets reread and
rewritten.  After rewriting an entry run ``--restamp MODULE ...``.

Paper locations (arXiv page) in the green-box titles are looked up in
``sources/yaacov_pedersen_2010_vision.md``; the box text itself is a paraphrase,
never a verbatim quotation.

Usage (repo root)::

    python3 scripts/scaffold_continuousfol_writeup.py [--check]
    python3 scripts/scaffold_continuousfol_writeup.py --restamp Completeness/CompletenessPre ...
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "ContinuousFOL"
WRITEUP = ROOT / "ContinuousFOL"
DB_PATH = WRITEUP / "module_writeup.json"
VISION = ROOT / "sources" / "yaacov_pedersen_2010_vision.md"
SOURCE_LABEL = "Ben Yaacov–Pedersen (2010)"

SECTION_TITLES = {
    1: "§1 Introduction",
    2: "§2 Łukasiewicz logic and continuous logic",
    3: "§3 Axioms: Group 1",
    4: "§4 Black-box theorems",
    5: "§5 Language and semantics of continuous first-order logic",
    6: "§6 Substitution and metric completions",
    7: "§7 Axioms: Group 2",
    8: "§8 The essentials",
    9: "§9 A proof of completeness",
}

FOLDER_SECTION = {
    "Introduction": 1,
    "LukasiewiczAndContinuous": 2,
    "Group1Axioms": 3,
    "BlackBox": 4,
    "LanguageAndSemantics": 5,
    "SubstitutionAndCompletions": 6,
    "Group2Axioms": 7,
    "Essentials": 8,
    "Completeness": 9,
}

# Modules whose writeup section differs from their Lean folder.  The propositional
# proof machinery in LukasiewiczAndContinuous/ (deduction theorems, soundness,
# MV-algebras, Chang's completeness theorem, ...) is what proves the §4 Facts, and
# it imports the §3 axiom systems, so it is written up in §4.
SECTION_2_KEEP = {
    "LukasiewiczAndContinuous/LukPropForm",
    "LukasiewiczAndContinuous/LukPropFormEval",
    "LukasiewiczAndContinuous/LukPropFormModels",
    "LukasiewiczAndContinuous/CLPropForm",
    "LukasiewiczAndContinuous/CLPropFormEval",
    "LukasiewiczAndContinuous/CLPropFormModels",
}
# ProvableTsubOfInconsistentAdjoin lives in Completeness/ but only imports §7/§8
# material, is cited as "cf. the proof of Lemma 8.5" and is imported by the §8
# module ConsistentAdjoin, so it is written up in §8 (no §8 <-> §9 cycle).
MODULE_SECTION = {"Basic": 1, "Completeness/ProvableTsubOfInconsistentAdjoin": 8}

LEAN_IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+ContinuousFOL\.(\S+)", re.M)
REF_RE = re.compile(
    r"\b(Definition|Theorem|Lemma|Proposition|Remark|Corollary|Fact|Notation)\s+(\d+\.\d+)"
)


def all_modules() -> list[str]:
    return sorted(
        str(p.relative_to(LEAN_DIR).with_suffix(""))
        for p in LEAN_DIR.rglob("*.lean")
    )


def section_of(mod: str) -> int:
    if mod in MODULE_SECTION:
        return MODULE_SECTION[mod]
    folder = mod.split("/")[0]
    if folder == "LukasiewiczAndContinuous" and mod not in SECTION_2_KEEP:
        return 4
    if folder not in FOLDER_SECTION:
        raise SystemExit(f"{mod}.lean has no writeup section: add it to MODULE_SECTION")
    return FOLDER_SECTION[folder]


def leaf_name(mod: str) -> str:
    parts = mod.split("/")
    return "_".join(parts[1:]) if len(parts) > 1 else parts[0]


def lean_text(mod: str) -> str:
    return (LEAN_DIR / f"{mod}.lean").read_text(encoding="utf-8")


def lean_sha(mod: str) -> str:
    return hashlib.sha256((LEAN_DIR / f"{mod}.lean").read_bytes()).hexdigest()


def imports_of(mod: str) -> list[str]:
    return [m.replace(".", "/") for m in LEAN_IMPORT_RE.findall(lean_text(mod))]


def topo_order(mods: list[str]) -> list[str]:
    """Lean import order (prerequisites first), ties broken alphabetically."""
    mset = set(mods)
    done: list[str] = []
    seen: set[str] = set()

    def visit(m: str) -> None:
        if m in seen:
            return
        seen.add(m)
        for d in sorted(imports_of(m)):
            if d in mset:
                visit(d)
        done.append(m)

    for m in sorted(mods):
        visit(m)
    return done


# --- paper locations -------------------------------------------------------

_REF_PAGES: dict[str, int] | None = None


def ref_pages() -> dict[str, int]:
    global _REF_PAGES
    if _REF_PAGES is None:
        _REF_PAGES = {}
        page = 0
        for line in VISION.read_text(encoding="utf-8").splitlines():
            m = re.match(r"<!--\s*page\s+(\d+)\s*-->", line.strip())
            if m:
                page = int(m.group(1))
                continue
            m = re.match(r"^\*{1,2}(\w+)\s+(\d+\.\d+)", line)
            if m:
                _REF_PAGES.setdefault(f"{m.group(1)} {m.group(2)}", page)
    return _REF_PAGES


GREEN_DIV = (
    '<div class="sourcequote" style="border:1px solid #2f7d57; background:#eef7f1; '
    'border-radius:4px; padding:0.1em 0.9em; margin:0.7em 0;">'
)

PROBLEMS: list[str] = []


def format_math(mod: str, boxes: list[dict]) -> str:
    parts = []
    for b in boxes:
        ref = b["ref"]
        page = b.get("page") or ref_pages().get(ref)
        if page is None:
            PROBLEMS.append(f"{mod}: paper location {ref!r} not found in vision OCR")
            loc = ref
        else:
            loc = f"arXiv p. {page}, {ref}"
        parts.append(
            f"{GREEN_DIV}\n\n**{SOURCE_LABEL}, {loc} (paraphrase)**\n\n"
            f"{b['text'].strip()}\n\n</div>\n"
        )
    return "\n".join(parts)


# --- writers -------------------------------------------------------------------

STALE: list[str] = []
MISSING: list[str] = []


def write_leaf(sec: int, mod: str, entry: dict | None) -> str:
    leaf = leaf_name(mod)
    out = WRITEUP / f"Section{sec}"
    out.mkdir(parents=True, exist_ok=True)
    if entry is None:
        MISSING.append(mod)
        entry = {"title": mod.split("/")[-1], "summary": "", "english": "", "paper": []}
    elif entry.get("lean_sha256") != lean_sha(mod):
        STALE.append(mod)
    title = entry["title"]
    math = out / f"{leaf}_math.txt"
    if entry.get("paper"):
        math.write_text(format_math(mod, entry["paper"]), encoding="utf-8")
    elif math.exists():
        math.unlink()
    (out / f"{leaf}_aisummary.txt").write_text(entry["summary"].strip() + "\n", encoding="utf-8")
    (out / f"{leaf}_ailean.txt").write_text(entry["english"].strip() + "\n", encoding="utf-8")
    depth = "../" * 2
    lines = [f"# {title}", ""]
    if math.exists():
        lines += [f'@import "{leaf}_math.txt" {{code_block=false}}', ""]
    lines += [
        f'@import "{leaf}_aisummary.txt" {{code_block=false}}',
        "",
        f'@import "{leaf}_ailean.txt" {{code_block=false}}',
        "",
        f"**[ContinuousFOL/{mod}.lean]({depth}ContinuousFOL/{mod}.lean)**",
        "",
        f'@import "{depth}ContinuousFOL/{mod}.lean"',
        "",
    ]
    (out / f"{leaf}.md").write_text("\n".join(lines), encoding="utf-8")
    return title


def _dot_escape(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def build_section_svg(sec: int, mods: list[str], titles: dict[str, str]) -> None:
    mset = set(mods)
    lines = [
        f"digraph Section{sec} {{",
        '  graph [rankdir=TD, bgcolor="white", pad="0.2", nodesep="0.35", ranksep="0.55"];',
        '  node [shape=box, style="rounded,filled", fillcolor="#ecfdf5",',
        '        color="#047857", fontname="Helvetica", fontsize=10,',
        '        fontcolor="#064e3b", margin="0.12,0.08"];',
        '  edge [color="#64748b", arrowsize=0.6];',
        "",
    ]
    for m in mods:
        lines.append(
            f'  "{m}" [label="{_dot_escape(titles[m])}", '
            f'URL="Section{sec}/{leaf_name(m)}.md", tooltip="{m}.lean"];'
        )
    lines.append("")
    for m in mods:
        for d in sorted(set(imports_of(m))):
            if d in mset and d != m:
                lines.append(f'  "{d}" -> "{m}";')
    lines.append("}")
    dot = WRITEUP / f"Section{sec}.dot"
    svg = WRITEUP / f"Section{sec}.svg"
    dot.write_text("\n".join(lines) + "\n", encoding="utf-8")
    try:
        subprocess.run(["dot", "-Tsvg", "-o", str(svg), str(dot)], check=True)
    except (FileNotFoundError, subprocess.CalledProcessError) as e:
        print(f"  warn: could not build {svg.name}: {e}", file=sys.stderr)


def write_barrel(sec: int, mods: list[str], titles: dict[str, str], sections: dict) -> None:
    meta = sections.get(str(sec), {})
    title = SECTION_TITLES[sec]
    # Chapter headings name the paper's own section, e.g. "Yaacov–Pedersen §1 Introduction".
    lines = [f"# Yaacov–Pedersen {title}", ""]
    if meta.get("blurb"):
        lines += [meta["blurb"].strip(), ""]
    if meta.get("notes"):
        lines += [meta["notes"].strip(), ""]
    lines += [
        f'@import "Section{sec}.svg" {{code_block=false, caption="Module dependencies within Yaacov–Pedersen {title.split()[0]}"}}',
        "",
        "Subsections follow Lean import order; labels are mathematical English.",
        "",
    ]
    for m in mods:
        lines.append(f"- [{titles[m]}](Section{sec}/{leaf_name(m)}.md)")
    lines.append("")
    (WRITEUP / f"Section{sec}.md").write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    db = json.loads(DB_PATH.read_text(encoding="utf-8")) if DB_PATH.is_file() else {}
    modules_db = db.setdefault("modules", {})
    if sys.argv[1:2] == ["--restamp"]:
        for mod in sys.argv[2:]:
            modules_db[mod]["lean_sha256"] = lean_sha(mod)
        DB_PATH.write_text(json.dumps(db, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
        print("restamped", ", ".join(sys.argv[2:]))
        return 0
    check = "--check" in sys.argv[1:]
    by_sec: dict[int, list[str]] = {s: [] for s in SECTION_TITLES}
    for mod in all_modules():
        by_sec[section_of(mod)].append(mod)
    total = 0
    for sec, mods in by_sec.items():
        mods = topo_order(mods)
        titles = {m: write_leaf(sec, m, modules_db.get(m)) for m in mods}
        write_barrel(sec, mods, titles, db.get("sections", {}))
        build_section_svg(sec, mods, titles)
        total += len(mods)
        print(f"Section{sec}: {len(mods)} modules")
    extra = set(modules_db) - set(all_modules())
    if extra:
        PROBLEMS.append("entries for missing modules: " + ", ".join(sorted(extra)))
    print(f"scaffolded {total} leaves")
    for p in PROBLEMS:
        print("PROBLEM:", p)
    if MISSING:
        print("MISSING WRITEUP:", ", ".join(MISSING))
    if STALE:
        print("STALE WRITEUP (Lean changed since written):", ", ".join(STALE))
    if check and (MISSING or STALE or PROBLEMS):
        return 1
    return 0


def extract_paper_blocks(lean_text: str) -> list[tuple[str, str]]:
    """Paper references named in declaration docstrings, as (ascription, "")."""
    out: list[tuple[str, str]] = []
    for m in re.finditer(r"/--?([\s\S]*?)-/", lean_text):
        for r in REF_RE.finditer(m.group(1)[:200]):
            a = f"{r.group(1)} {r.group(2)}"
            if (a, "") not in out:
                out.append((a, ""))
    return out


if __name__ == "__main__":
    raise SystemExit(main())
