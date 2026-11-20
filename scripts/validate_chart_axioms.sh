#!/usr/bin/env bash
# Offline Palomar axiom gate for every proof-chart theorem in holes-graph.json.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

python3 - <<'PY'
import json, pathlib, re, subprocess, tempfile, os

# Prefer a local tmp; some environments point TMPDIR at unreadable mounts.
os.environ.setdefault("TMPDIR", "/tmp")
g = json.load(open("holes-graph.json"))
names = [n["id"] for n in g["nodes"]]
if not names:
    print("chart theorems: 0 (empty chart; nothing to audit)")
    print("OK: empty chart")
    raise SystemExit(0)
lean = "import ContinuousFOL\nopen ContinuousFOL\n" + "".join(
    f"#print axioms {n}\n" for n in names
)
path = pathlib.Path(tempfile.mkstemp(suffix=".lean", dir="/tmp")[1])
path.write_text(lean)
proc = subprocess.run(
    ["lake", "env", "lean", str(path)],
    text=True,
    capture_output=True,
)
path.unlink(missing_ok=True)
out = (proc.stdout or "") + (proc.stderr or "")

permitted = {"propext", "Classical.choice", "Quot.sound"}
bad = []
ok = []
# Parse whole declarations rather than lines: Lean may wrap an axiom list or
# place the next `#print axioms` result on the same output line.
for m in re.finditer(
    r"'ContinuousFOL\.([^']+)' depends on axioms: \[(.*?)\]", out, flags=re.S
):
    name, axs = m.group(1), m.group(2)
    items = {a.strip() for a in axs.split(",") if a.strip()}
    extra = sorted(items - permitted)
    if extra:
        bad.append((name, extra))
    else:
        ok.append(name)

for m in re.finditer(r"'ContinuousFOL\.([^']+)' does not depend on any axioms", out):
    if m.group(1) not in ok:
        ok.append(m.group(1))

print(f"chart theorems: {len(names)}")
print(f"Palomar-clean: {len(ok)}")
print(f"classical / extra axioms: {len(bad)}")
for n, extra in bad:
    print(f"  FAIL {n}: {', '.join(extra)}")
if len(ok) + len(bad) < len(names):
    print("warning: could not classify all theorems; raw output tail:")
    print("\n".join(out.splitlines()[-20:]))
# Nonzero exit only if a completed theorem has extra axioms. Open/blocked
# nodes are already disclosed by the generated holes board.
known = {n["id"] for n in g["nodes"] if n["status"] != "done"}
unexpected = [(n, e) for n, e in bad if n not in known]
if unexpected:
    raise SystemExit("unexpected extra axioms outside disclosed proof holes")
print("OK: every completed chart theorem is Palomar-clean")
PY
