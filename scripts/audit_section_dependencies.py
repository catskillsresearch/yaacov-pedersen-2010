#!/usr/bin/env python3
"""Audit ContinuousFOL section deps: section aggregation versus the actual Lean import DAG.

Run from any directory: python3 scripts/audit_section_dependencies.py
An arrow importer -> imported has the same direction as section_deps_graph.py.
"""
from collections import defaultdict
import section_deps_graph as graph


def main():
    sections = graph.section_leans()
    placement = {m: sec for sec, modules in sections.items() for m in modules}
    imports = {m: graph.lean_imports(m) & placement.keys() for m in placement}
    active, done = set(), set()

    def visit(m, path):
        if m in active:
            raise SystemExit("LEAN IMPORT CYCLE: " + " -> ".join(path + [m]))
        if m in done:
            return
        active.add(m)
        for dep in sorted(imports[m]):
            visit(dep, path + [m])
        active.remove(m)
        done.add(m)

    for m in sorted(imports):
        visit(m, [])
    print(f"Module graph: {len(imports)} modules; no Lean import cycles.")
    edges = defaultdict(list)
    for m in sorted(imports):
        for dep in sorted(imports[m]):
            a, b = placement[m], placement[dep]
            if a != b:
                edges[a, b].append((m, dep))
    print(f"Figure 1: {len(edges)} directed section edges "
          "(drawn from the imported section to the importing section).")
    print("Reciprocal section pairs (these are aggregation cycles, not Lean cycles):")
    if not any((b, a) in edges for a, b in edges):
        print("  (none)")
    for a, b in sorted(edges):
        if a < b and (b, a) in edges:
            print(f"  Section {a} <-> Section {b}")
            for s, t in [(a, b), (b, a)]:
                print(f"    Section {s} imports from Section {t}: "
                      f"{len(edges[s,t])} direct module imports")
                for m, dep in edges[s,t]:
                    print(f"      {m} imports {dep}")


if __name__ == "__main__":
    main()
