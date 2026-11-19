#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Syntactic dependency graph of Lean definitions and theorems.

Walks project .lean sources (not vendor/, .lake/, or *skeleton_backup*),
finds named declarations, and draws an edge B -> A when A's type or body
mentions B (arrows point from a prerequisite to the declaration that uses
it). This is a syntactic approximation, not a Lean kernel analysis.

Usage (from a yaacov-pedersen-2010 repo root):

    python3 scripts/lean_deps_graph.py
    python3 scripts/lean_deps_graph.py /path/to/repo /path/to/out.svg

Defaults: repo = parent of this script's directory (or cwd), output =
<repo>/../yaacov-pedersen-2010_deps.svg. If `dot` (graphviz) is on PATH, writes the
SVG; otherwise writes a .dot file next to the intended SVG and prints
install instructions. Pass --png to also write a PNG next to the SVG.
"""

from __future__ import annotations

import argparse
import html
import os
import shutil
import subprocess
import sys
import unicodedata
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Iterator, Optional


DECL_KEYWORDS = frozenset({
    "def", "theorem", "lemma", "abbrev", "structure", "inductive", "class",
    "instance", "opaque", "axiom",
})
MODIFIERS = frozenset({
    "private", "protected", "noncomputable", "unsafe", "partial", "public",
    "local", "scoped", "meta",
})
# Commands that start a new top-level command (when delimiter depth is 0).
COMMAND_KEYWORDS = frozenset({
    "namespace", "section", "end", "import", "open", "variable", "set_option",
    "universe", "include", "omit", "export", "example", "module", "mutual",
    "syntax", "macro", "macro_rules", "elab", "elab_rules", "notation",
    "prefix", "infix", "infixl", "infixr", "postfix", "attribute",
    "initialize", "builtin_initialize", "class", "structure", "inductive",
    "def", "theorem", "lemma", "abbrev", "instance", "opaque", "axiom",
    "alias", "abbrev",
})
# Opening/closing delimiters that nest terms.
OPEN_DELIMS = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE_DELIMS = {")": "(", "]": "[", "}": "{", "⟩": "⟨"}

# Light fills with dark text; qualitatively distinct.
FILE_COLORS = [
    "#8dd3c7", "#ffffb3", "#bebada", "#fb8072", "#80b1d3",
    "#fdb462", "#b3de69", "#fccde5", "#ccebc5", "#bc80bd",
    "#ffed6f", "#a6cee3", "#b2df8a", "#fdbf6f", "#cab2d6",
    "#fb9a99", "#9ecae1", "#c7e9c0", "#fdd0a2", "#bcbddc",
    "#d9d9d9", "#fa9fb5", "#fec44f", "#99d8c9",
]


@dataclass(frozen=True)
class Token:
    kind: str  # ident, string, number, symbol
    value: str
    line: int  # 1-based
    col: int   # 1-based


@dataclass
class Decl:
    full_name: str
    short_name: str
    source_name: str  # name as written after the keyword (may be dotted)
    kind: str         # def/theorem/... or "field" / "ctor"
    file: Path
    file_root: str
    line: int
    private: bool
    has_sorry: bool = False
    body: list[Token] = field(default_factory=list)


def is_ident_start(ch: str) -> bool:
    if not ch:
        return False
    if ch == "_" or ch.isalpha():
        return True
    cat = unicodedata.category(ch)
    return cat.startswith("L")


def is_ident_cont(ch: str) -> bool:
    if not ch:
        return False
    if ch.isalnum() or ch in "_'!?":
        return True
    cat = unicodedata.category(ch)
    return cat.startswith("L") or cat.startswith("N") or cat in {"Mn", "Mc", "Lm"}


def tokenize(src: str) -> list[Token]:
    """Tokenize Lean source, dropping comments. Strings become string tokens."""
    n = len(src)
    i = 0
    line = 1
    col = 1
    out: list[Token] = []

    def peek(k: int = 0) -> str:
        j = i + k
        return src[j] if j < n else ""

    def bump(cnt: int = 1) -> None:
        nonlocal i, line, col
        for _ in range(cnt):
            if i < n:
                if src[i] == "\n":
                    line += 1
                    col = 1
                else:
                    col += 1
                i += 1

    while i < n:
        ch = src[i]
        sl, sc = line, col

        # whitespace
        if ch.isspace():
            bump()
            continue

        # line comment
        if ch == "-" and peek(1) == "-":
            while i < n and src[i] != "\n":
                bump()
            continue

        # block comment (nested), including /-- docs
        if ch == "/" and peek(1) == "-":
            depth = 1
            bump(2)
            while i < n and depth:
                if peek() == "/" and peek(1) == "-":
                    depth += 1
                    bump(2)
                elif peek() == "-" and peek(1) == "/":
                    depth -= 1
                    bump(2)
                else:
                    bump()
            continue

        # string literal
        if ch == '"':
            bump()
            val = ['"']
            while i < n:
                c = src[i]
                val.append(c)
                if c == "\\" and i + 1 < n:
                    bump()
                    val.append(src[i] if i < n else "")
                    bump()
                    continue
                bump()
                if c == '"':
                    break
            out.append(Token("string", "".join(val), sl, sc))
            continue

        # escaped identifier «...»
        if ch == "«":
            bump()
            chars: list[str] = []
            while i < n and src[i] != "»":
                chars.append(src[i])
                bump()
            if i < n and src[i] == "»":
                bump()
            out.append(Token("ident", "".join(chars).strip(), sl, sc))
            continue

        # identifier
        if is_ident_start(ch):
            chars = [ch]
            bump()
            while is_ident_cont(peek()):
                chars.append(src[i])
                bump()
            out.append(Token("ident", "".join(chars), sl, sc))
            continue

        # number (including 1e-15, 0xFF — keep it simple)
        if ch.isdigit():
            chars = [ch]
            bump()
            while True:
                c = peek()
                if c.isdigit() or c in ".eE":
                    chars.append(c)
                    bump()
                elif c in "+-" and chars[-1] in "eE":
                    chars.append(c)
                    bump()
                else:
                    break
            out.append(Token("number", "".join(chars), sl, sc))
            continue

        # everything else is a one-character symbol
        out.append(Token("symbol", ch, sl, sc))
        bump()

    return out


def read_dotted_name(tokens: list[Token], i: int) -> tuple[str, int]:
    """Read ident(.ident)* starting at i. Returns (name, index_after)."""
    if i >= len(tokens) or tokens[i].kind != "ident":
        return "", i
    parts = [tokens[i].value]
    i += 1
    while (
        i + 1 < len(tokens)
        and tokens[i].kind == "symbol"
        and tokens[i].value == "."
        and tokens[i + 1].kind == "ident"
    ):
        parts.append(tokens[i + 1].value)
        i += 2
    return ".".join(parts), i


def skip_matching(tokens: list[Token], i: int) -> int:
    """i points at an opening delimiter; return index after the matching close."""
    if i >= len(tokens):
        return i
    opener = tokens[i].value
    closer = OPEN_DELIMS.get(opener)
    if closer is None:
        return i + 1
    depth = 1
    i += 1
    while i < len(tokens) and depth:
        t = tokens[i]
        if t.kind == "symbol":
            if t.value in OPEN_DELIMS:
                depth += 1
            elif t.value == closer:
                depth -= 1
        i += 1
    return i


def skip_attributes_and_modifiers(tokens: list[Token], i: int) -> tuple[int, bool]:
    """Skip @[...] attributes and modifiers. Return (new_i, is_private)."""
    is_private = False
    n = len(tokens)
    while i < n:
        t = tokens[i]
        # attributes
        if t.kind == "symbol" and t.value == "@":
            if i + 1 < n and tokens[i + 1].kind == "symbol" and tokens[i + 1].value == "[":
                i = skip_matching(tokens, i + 1)
                continue
            i += 1
            continue
        if t.kind == "ident" and t.value in MODIFIERS:
            nxt = tokens[i + 1] if i + 1 < n else None
            # "noncomputable section", "public section", "public import"
            if t.value == "noncomputable" and nxt and nxt.kind == "ident" and nxt.value == "section":
                break
            if t.value == "public" and nxt and nxt.kind == "ident" and nxt.value in {"section", "import"}:
                break
            if t.value == "private":
                is_private = True
            i += 1
            continue
        break
    return i, is_private


def at_command_start(tokens: list[Token], i: int) -> bool:
    """True if tokens[i] (after attrs/modifiers) looks like a command keyword."""
    j, _ = skip_attributes_and_modifiers(tokens, i)
    if j >= len(tokens):
        return False
    t = tokens[j]
    if t.kind == "ident" and t.value in COMMAND_KEYWORDS:
        return True
    # hash commands: #check, #eval, ...
    if t.kind == "symbol" and t.value == "#":
        return True
    return False


def collect_body(tokens: list[Token], i: int) -> tuple[list[Token], int]:
    """Collect tokens from i until the next depth-0 command. Return (body, next_i)."""
    body: list[Token] = []
    depth = 0
    n = len(tokens)
    while i < n:
        if depth == 0 and at_command_start(tokens, i):
            break
        t = tokens[i]
        body.append(t)
        if t.kind == "symbol":
            if t.value in OPEN_DELIMS:
                depth += 1
            elif t.value in CLOSE_DELIMS and depth > 0:
                depth -= 1
        i += 1
    return body, i


def qualify(ns_stack: list[str], name: str) -> str:
    prefix = ".".join(p for p in ns_stack if p)
    return f"{prefix}.{name}" if prefix else name


def short_label(full_name: str) -> str:
    prefix = "ContinuousFOL."
    if full_name.startswith(prefix):
        return full_name[len(prefix):]
    return full_name


def parse_structure_like_fields(
    body: list[Token],
    parent_full: str,
    parent_short: str,
    kind: str,
    file: Path,
    file_root: str,
    is_private: bool,
    ns_stack: list[str],
) -> list[Decl]:
    """Extract structure/class fields or inductive constructors from a body."""
    fields: list[Decl] = []
    i = 0
    n = len(body)
    # Find `where` or `:=` at depth 0 to start the field list.
    depth = 0
    start = 0
    found = False
    while i < n:
        t = body[i]
        if t.kind == "symbol":
            if t.value in OPEN_DELIMS:
                depth += 1
            elif t.value in CLOSE_DELIMS and depth > 0:
                depth -= 1
            elif depth == 0 and t.value == "=" and i + 1 < n and body[i + 1].kind == "symbol" and body[i + 1].value == ":":
                # shouldn't happen; Lean uses := as two symbols ':' '='
                pass
            elif depth == 0 and t.value == ":" and i + 1 < n and body[i + 1].kind == "symbol" and body[i + 1].value == "=":
                start = i + 2
                found = True
                break
        if t.kind == "ident" and t.value == "where" and depth == 0:
            start = i + 1
            found = True
            break
        i += 1
    if not found:
        return fields

    i = start
    depth = 0
    if kind == "ctor":
        # inductive: | name ...
        while i < n:
            t = body[i]
            if t.kind == "ident" and t.value == "deriving" and depth == 0:
                break
            if t.kind == "symbol" and t.value == "|" and depth == 0:
                i += 1
                if i < n and body[i].kind == "ident":
                    nm = body[i].value
                    full = f"{parent_full}.{nm}"
                    fields.append(Decl(
                        full_name=full,
                        short_name=short_label(full),
                        source_name=nm,
                        kind="ctor",
                        file=file,
                        file_root=file_root,
                        line=body[i].line,
                        private=is_private,
                    ))
                    i += 1
                    continue
            if t.kind == "symbol":
                if t.value in OPEN_DELIMS:
                    depth += 1
                elif t.value in CLOSE_DELIMS and depth > 0:
                    depth -= 1
            i += 1
        return fields

    # structure / class fields: ident binders* : type  at depth 0
    # Require `:` immediately after the name and any binders so a type
    # like `ℝ` on one line is not taken as the next field just because
    # the following field has a `:`.
    while i < n:
        t = body[i]
        if t.kind == "ident" and t.value == "deriving" and depth == 0:
            break
        if t.kind == "symbol":
            if t.value in OPEN_DELIMS:
                # old syntax: (field : type)
                if t.value == "(" and depth == 0:
                    j = i + 1
                    if j < n and body[j].kind == "ident":
                        nm = body[j].value
                        full = f"{parent_full}.{nm}"
                        fields.append(Decl(
                            full_name=full,
                            short_name=short_label(full),
                            source_name=nm,
                            kind="field",
                            file=file,
                            file_root=file_root,
                            line=body[j].line,
                            private=is_private,
                        ))
                    i = skip_matching(body, i)
                    continue
                depth += 1
                i += 1
                continue
            if t.value in CLOSE_DELIMS and depth > 0:
                depth -= 1
                i += 1
                continue
        if t.kind == "ident" and depth == 0 and t.value not in {"where", "with", "extends", "deriving"}:
            nm = t.value
            j = i + 1
            while j < n and body[j].kind == "symbol" and body[j].value in OPEN_DELIMS:
                j = skip_matching(body, j)
            if j < n and body[j].kind == "symbol" and body[j].value == ":":
                full = f"{parent_full}.{nm}"
                fields.append(Decl(
                    full_name=full,
                    short_name=short_label(full),
                    source_name=nm,
                    kind="field",
                    file=file,
                    file_root=file_root,
                    line=t.line,
                    private=is_private,
                ))
            i += 1
            continue
        i += 1
    return fields


def body_has_sorry(body: list[Token]) -> bool:
    return any(t.kind == "ident" and t.value == "sorry" for t in body)


def parse_file(path: Path, repo: Path) -> list[Decl]:
    src = path.read_text(encoding="utf-8")
    tokens = tokenize(src)
    try:
        rel = path.relative_to(repo)
    except ValueError:
        rel = path
    file_root = path.stem
    decls: list[Decl] = []

    ns_stack: list[str] = []  # empty string = anonymous section
    i = 0
    n = len(tokens)

    while i < n:
        # skip stray symbols that aren't commands
        if not at_command_start(tokens, i):
            i += 1
            continue

        j, is_private = skip_attributes_and_modifiers(tokens, i)
        if j >= n:
            break
        t = tokens[j]

        # #commands
        if t.kind == "symbol" and t.value == "#":
            # consume until next command at depth 0, starting after this one
            _, i = collect_body(tokens, j + 2 if j + 1 < n else j + 1)
            continue

        if t.kind != "ident":
            i = j + 1
            continue
        kw = t.value

        if kw in {"import"} or (kw == "public" and j + 1 < n and tokens[j + 1].value == "import"):
            _, i = collect_body(tokens, j + 1)
            continue

        if kw == "public" and j + 1 < n and tokens[j + 1].value == "section":
            ns_stack.append("")
            i = j + 2
            continue

        if kw == "noncomputable" and j + 1 < n and tokens[j + 1].value == "section":
            ns_stack.append("")
            i = j + 2
            continue

        if kw == "section":
            name, k = read_dotted_name(tokens, j + 1)
            # named sections do not contribute to declaration names
            ns_stack.append("")
            i = k
            continue

        if kw == "namespace":
            name, k = read_dotted_name(tokens, j + 1)
            if name:
                ns_stack.append(name)
            i = k
            continue

        if kw == "end":
            name, k = read_dotted_name(tokens, j + 1)
            if name:
                # pop until we find a matching namespace (skip anonymous sections)
                while ns_stack:
                    top = ns_stack.pop()
                    if top == name:
                        break
            else:
                if ns_stack:
                    ns_stack.pop()
            i = k
            continue

        if kw == "mutual":
            i = j + 1
            continue

        if kw == "module":
            i = j + 1
            continue

        if kw in DECL_KEYWORDS:
            name, k = read_dotted_name(tokens, j + 1)
            if kw == "instance" and not name:
                # unnamed instance: skip, but still consume its body
                _, i = collect_body(tokens, k)
                continue
            if not name:
                _, i = collect_body(tokens, k)
                continue
            full = qualify(ns_stack, name)
            body, i = collect_body(tokens, k)
            d = Decl(
                full_name=full,
                short_name=short_label(full),
                source_name=name,
                kind=kw,
                file=path,
                file_root=file_root,
                line=t.line,
                private=is_private,
                has_sorry=body_has_sorry(body),
                body=body,
            )
            decls.append(d)
            if kw in {"structure", "class"}:
                decls.extend(parse_structure_like_fields(
                    body, full, d.short_name, "field", path, file_root, is_private, ns_stack,
                ))
            elif kw == "inductive":
                decls.extend(parse_structure_like_fields(
                    body, full, d.short_name, "ctor", path, file_root, is_private, ns_stack,
                ))
            continue

        # other commands (open, variable, set_option, ...)
        _, i = collect_body(tokens, j + 1)

    return decls


def iter_project_lean_files(repo: Path) -> list[Path]:
    files: list[Path] = []
    root_mod = repo / "ContinuousFOL.lean"
    if root_mod.is_file():
        files.append(root_mod)
    src_dir = repo / "ContinuousFOL"
    if src_dir.is_dir():
        files.extend(sorted(src_dir.rglob("*.lean")))
    out: list[Path] = []
    for p in files:
        rel = p.relative_to(repo).as_posix()
        if rel.startswith("vendor/") or "/vendor/" in rel:
            continue
        if rel.startswith(".lake/") or "/.lake/" in rel:
            continue
        if p.name.endswith("skeleton_backup.lean") or "skeleton_backup" in p.name:
            continue
        out.append(p)
    return out


def dotted_spans(tokens: list[Token]) -> list[tuple[str, bool, int, int]]:
    """Yield (dotted_name, is_dotted, start_index, end_index_exclusive) left-to-right, greedy."""
    spans: list[tuple[str, bool, int, int]] = []
    i = 0
    n = len(tokens)
    while i < n:
        if tokens[i].kind == "ident":
            name, j = read_dotted_name(tokens, i)
            spans.append((name, "." in name, i, j))
            i = j
        else:
            i += 1
    return spans


def resolve_references(decls: list[Decl]) -> list[tuple[str, str]]:
    """Return edges (src_full, dst_full), no self-loops, unique."""
    by_full: dict[str, Decl] = {}
    # If two decls somehow share a full name, keep the first and still index both for lookup.
    all_by_full: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        all_by_full[d.full_name].append(d)
        by_full.setdefault(d.full_name, d)

    # last-component and source-name indexes
    by_last: dict[str, list[Decl]] = defaultdict(list)
    by_source: dict[str, list[Decl]] = defaultdict(list)
    by_short: dict[str, list[Decl]] = defaultdict(list)
    for d in decls:
        last = d.full_name.split(".")[-1]
        by_last[last].append(d)
        by_source[d.source_name].append(d)
        by_short[d.short_name].append(d)
        # also index TableParams.T under "TableParams.T"
        if d.short_name != last:
            by_short[d.short_name].append(d)

    def visible_candidates(cands: Iterable[Decl], from_file: Path) -> list[Decl]:
        seen: list[Decl] = []
        ids = set()
        for d in cands:
            if d.private and d.file != from_file:
                continue
            key = (d.full_name, str(d.file), d.line)
            if key in ids:
                continue
            ids.add(key)
            seen.append(d)
        return seen

    def pick(cands: list[Decl], from_file: Path, prefer_same_file: bool = True) -> Optional[Decl]:
        vis = visible_candidates(cands, from_file)
        if not vis:
            return None
        if len(vis) == 1:
            return vis[0]
        if prefer_same_file:
            same = [d for d in vis if d.file == from_file]
            if len(same) == 1:
                return same[0]
        return None  # ambiguous

    def lookup(name: str, from_file: Path, dotted: bool) -> Optional[Decl]:
        # Exact full name
        if name in all_by_full:
            return pick(all_by_full[name], from_file)
        # Qualified with ContinuousFOL prefix
        prefixed = f"ContinuousFOL.{name}"
        if prefixed in all_by_full:
            return pick(all_by_full[prefixed], from_file)
        # Unique suffix / short name, but only for qualified references
        # (TableClaim.certified, ContinuousFOL.Zproc). Never treat a bare
        # ident such as σ, T, hi, ℕ as a match for a structure field.
        if dotted or "." in name:
            suffix_hits = [
                d for d in decls
                if d.full_name.endswith("." + name) or d.short_name == name
            ]
            got = pick(suffix_hits, from_file)
            if got:
                return got
            # last component: unique field/ctor (dot projection), else unique decl
            last = name.split(".")[-1]
            fields = [d for d in by_last.get(last, []) if d.kind in {"field", "ctor"}]
            got = pick(fields, from_file)
            if got:
                return got
            regular = [d for d in by_last.get(last, []) if d.kind not in {"field", "ctor"}]
            return pick(regular, from_file)
        # Bare identifier: unique non-field/non-ctor declaration only
        regular = [d for d in by_source.get(name, []) if d.kind not in {"field", "ctor"}]
        if not regular:
            regular = [d for d in by_last.get(name, []) if d.kind not in {"field", "ctor"}]
        if not regular:
            regular = [d for d in by_short.get(name, []) if d.kind not in {"field", "ctor"}]
        return pick(regular, from_file)

    edges: set[tuple[str, str]] = set()
    for d in decls:
        for name, is_dotted, _a, _b in dotted_spans(d.body):
            tgt = lookup(name, d.file, is_dotted)
            if tgt is None:
                continue
            if tgt.full_name == d.full_name and tgt.file == d.file:
                continue
            edges.add((d.full_name, tgt.full_name))
    return sorted(edges)


def xml_escape(s: str) -> str:
    return html.escape(s, quote=True)


def node_id(i: int) -> str:
    return f"n{i}"


def pick_font() -> str:
    """Prefer a font with Greek/Unicode (e.g. TableParams.σ)."""
    candidates = [
        "DejaVu Sans", "Noto Sans", "Liberation Sans", "FreeSans",
        "Arial Unicode MS", "Helvetica", "Arial",
    ]
    try:
        out = subprocess.run(
            ["fc-list", ":", "family"],
            capture_output=True, text=True, timeout=5, check=False,
        )
        families = set()
        for line in out.stdout.splitlines():
            for part in line.split(","):
                families.add(part.strip())
        for c in candidates:
            if c in families:
                return c
    except (FileNotFoundError, subprocess.SubprocessError, OSError):
        pass
    return "Helvetica"



def emit_dot(decls: list[Decl], edges: list[tuple[str, str]], font: str | None = None) -> str:
    # Stable order: by file root, then line, then name
    decls_sorted = sorted(decls, key=lambda d: (d.file_root.lower(), d.line, d.full_name))
    font = font or pick_font()
    id_of: dict[tuple[str, str, int], str] = {}
    # full_name may collide for private decls; key by full+file+line
    key_of_full_file: dict[tuple[str, str], str] = {}
    lines: list[str] = []
    lines.append("digraph ContinuousFOLDeps {")
    lines.append(f"  graph [rankdir=LR, overlap=false, splines=true, nodesep=0.18, ranksep=0.45, fontsize=12, fontname=\"{font}\", bgcolor=\"white\", pad=\"0.3\", label=\"ContinuousFOL definition & theorem dependencies (syntactic)\", labelloc=t, labeljust=c];")
    lines.append(f"  node [shape=box, style=\"filled,rounded\", fontname=\"{font}\", fontsize=9, color=\"#333333\", penwidth=0.8, margin=\"0.08,0.04\"];")
    lines.append("  edge [color=\"#555555\", arrowsize=0.6, penwidth=0.7];")

    file_roots = sorted({d.file_root for d in decls_sorted}, key=str.lower)
    color_of = {fr: FILE_COLORS[i % len(FILE_COLORS)] for i, fr in enumerate(file_roots)}

    for i, d in enumerate(decls_sorted):
        nid = node_id(i)
        id_of[(d.full_name, str(d.file), d.line)] = nid
        key_of_full_file.setdefault((d.full_name, str(d.file)), nid)
        # If unique full name, also allow lookup by full name alone
        key_of_full_file.setdefault((d.full_name, ""), nid)
        fill = color_of[d.file_root]
        label = (
            f"<{xml_escape(d.short_name)}<BR/>"
            f'<FONT POINT-SIZE="8">{xml_escape(d.file_root)}</FONT>>'
        )
        extras = ""
        if d.has_sorry:
            extras = ' color="red" penwidth=3'
        # tooltip with kind and full name
        tip = xml_escape(f"{d.kind} {d.full_name} ({d.file_root}:{d.line})")
        lines.append(
            f'  {nid} [label={label}, fillcolor="{fill}", tooltip="{tip}"{extras}];'
        )

    def resolve_node(full: str, prefer_file: str = "") -> Optional[str]:
        if prefer_file and (full, prefer_file) in key_of_full_file:
            return key_of_full_file[(full, prefer_file)]
        # unique full name
        hits = [nid for (f, file), nid in key_of_full_file.items() if f == full and file]
        if len({nid for nid in hits}) == 1:
            return hits[0]
        return key_of_full_file.get((full, ""))

    # Map full names to a canonical node (public names are unique; privates keyed by file)
    full_to_nodes: dict[str, list[str]] = defaultdict(list)
    for d in decls_sorted:
        full_to_nodes[d.full_name].append(id_of[(d.full_name, str(d.file), d.line)])

    file_of_full: dict[str, Path] = {d.full_name: d.file for d in decls_sorted}

    seen_edge_ids: set[tuple[str, str]] = set()
    decl_by_full_file = {(d.full_name, str(d.file)): d for d in decls_sorted}
    for src, dst in edges:
        src_ids = full_to_nodes.get(src, [])
        dst_ids = full_to_nodes.get(dst, [])
        if not src_ids or not dst_ids:
            continue
        # If multiple (private collisions), connect all same-name nodes — rare
        for s in src_ids:
            for t in dst_ids:
                if s == t:
                    continue
                if (s, t) in seen_edge_ids:
                    continue
                seen_edge_ids.add((s, t))
                # s uses t: draw prerequisite t -> user s.
                lines.append(f"  {t} -> {s};")

    # Legend
    lines.append("")
    lines.append("  subgraph cluster_legend {")
    lines.append('    label="Legend: file colors  |  thick red border = body contains sorry";')
    lines.append(f"    style=rounded; color=\"#888888\"; fontsize=10; fontname=\"{font}\";")
    # Do not emit edges in the legend: invisible edges would participate
    # in ranking and stretch the main graph.
    lines.append('    node [shape=box, style="filled,rounded", fontsize=9, penwidth=0.8, color="#333333"];')
    for k, fr in enumerate(file_roots):
        lid = f"leg{k}"
        count = sum(1 for d in decls_sorted if d.file_root == fr)
        lines.append(
            f'    {lid} [label="{xml_escape(fr)} ({count})", fillcolor="{color_of[fr]}"];'
        )
    lines.append(
        '    leg_sorry [label="has sorry", fillcolor="white", color="red", penwidth=3];'
    )
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines) + "\n"


def find_dot() -> Optional[str]:
    found = shutil.which("dot")
    if found:
        return found
    # common extra location used when this script was first developed
    extra = Path("/tmp/conda/bin/dot")
    if extra.is_file() and os.access(extra, os.X_OK):
        return str(extra)
    return None


def render(dot_src: str, svg_path: Path, png_path: Optional[Path], dot_bin: Optional[str]) -> tuple[Path, Optional[Path], Path]:
    dot_path = svg_path.with_suffix(".dot")
    svg_path.parent.mkdir(parents=True, exist_ok=True)
    dot_path.write_text(dot_src, encoding="utf-8")
    wrote_svg = False
    wrote_png: Optional[Path] = None
    if not dot_bin:
        return svg_path, wrote_png, dot_path
    try:
        subprocess.run(
            [dot_bin, "-Tsvg", "-o", str(svg_path), str(dot_path)],
            check=True,
            capture_output=True,
            text=True,
        )
        wrote_svg = True
    except (subprocess.CalledProcessError, FileNotFoundError) as e:
        err = getattr(e, "stderr", "") or str(e)
        print(f"error: graphviz failed to write SVG:\n{err}", file=sys.stderr)
        return svg_path, wrote_png, dot_path
    if png_path is not None and wrote_svg:
        try:
            subprocess.run(
                [dot_bin, "-Tpng", "-Gdpi=120", "-o", str(png_path), str(dot_path)],
                check=True,
                capture_output=True,
                text=True,
            )
            wrote_png = png_path
        except (subprocess.CalledProcessError, FileNotFoundError) as e:
            err = getattr(e, "stderr", "") or str(e)
            print(f"warning: graphviz failed to write PNG:\n{err}", file=sys.stderr)
    return svg_path, wrote_png, dot_path


def default_repo() -> Path:
    here = Path(__file__).resolve()
    if here.parent.name == "scripts":
        return here.parent.parent
    return Path.cwd()


def parse_args(argv: list[str]) -> argparse.Namespace:
    p = argparse.ArgumentParser(
        description="Build a syntactic dependency SVG of Lean defs/theorems in a ContinuousFOL repo.",
    )
    p.add_argument(
        "repo",
        nargs="?",
        type=Path,
        default=None,
        help="Repo root (directory containing ContinuousFOL.lean). Default: parent of scripts/.",
    )
    p.add_argument(
        "output",
        nargs="?",
        type=Path,
        default=None,
        help="Output SVG path. Default: <repo>/../yaacov-pedersen-2010_deps.svg",
    )
    p.add_argument("--png", nargs="?", const=True, default=False, metavar="PATH",
                   help="Also write a PNG. Optional path; default is the SVG path with .png")
    p.add_argument("--dot-only", action="store_true", help="Write the .dot file and skip invoking graphviz")
    return p.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv if argv is not None else sys.argv[1:])
    repo = (args.repo or default_repo()).resolve()
    if not repo.is_dir():
        print(f"error: repo path is not a directory: {repo}", file=sys.stderr)
        return 2
    output = (args.output or (repo.parent / "yaacov-pedersen-2010_deps.svg")).resolve()

    files = iter_project_lean_files(repo)
    if not files:
        print(f"error: no ContinuousFOL .lean files found under {repo}", file=sys.stderr)
        return 2

    decls: list[Decl] = []
    for f in files:
        decls.extend(parse_file(f, repo))

    edges = resolve_references(decls)
    n_sorry = sum(1 for d in decls if d.has_sorry)
    file_roots = sorted({d.file_root for d in decls}, key=str.lower)
    isolated = 0
    used = set()
    for a, b in edges:
        used.add(a)
        used.add(b)
    # isolated among unique full names (privates with same name still count separately)
    keys = [(d.full_name, str(d.file), d.line) for d in decls]
    connected_fulls = used
    isolated = sum(1 for d in decls if d.full_name not in connected_fulls)

    print(f"repo:          {repo}")
    print(f"lean files:    {len(files)}")
    print(f"files w/ decls:{len(file_roots)}")
    print(f"nodes:         {len(decls)}")
    print(f"edges:         {len(edges)}")
    print(f"isolated:      {isolated}")
    print(f"sorry nodes:   {n_sorry}")
    print(f"excluded:      vendor/, .lake/, *skeleton_backup.lean")

    dot_src = emit_dot(decls, edges)
    png_path: Optional[Path] = None
    if args.png is True:
        png_path = output.with_suffix(".png")
    elif args.png:
        png_path = Path(args.png).resolve()

    dot_bin = None if args.dot_only else find_dot()
    svg_path, wrote_png, dot_path = render(dot_src, output, png_path, dot_bin)
    if dot_bin is None:
        print(f"wrote DOT:     {dot_path}")
        if not args.dot_only:
            print(
                "graphviz (`dot`) was not found on PATH.\n"
                "Install it (e.g. `sudo apt install graphviz` or `conda install -c conda-forge graphviz`)\n"
                f"then run:  dot -Tsvg -o {output} {dot_path}",
                file=sys.stderr,
            )
            return 3
        return 0

    if output.exists() and output.stat().st_size > 0:
        print(f"wrote SVG:     {svg_path}")
    print(f"wrote DOT:     {dot_path}")
    if wrote_png:
        print(f"wrote PNG:     {wrote_png}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
