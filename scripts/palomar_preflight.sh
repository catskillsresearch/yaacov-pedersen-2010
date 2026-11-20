#!/usr/bin/env bash
# Reproduce repository-side mechanical checks before Palomar submission.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"

find_toolkit() {
  local root="$1" d
  for d in \
    "${PALOMAR_PREFLIGHT_ROOT:-}" \
    "$(dirname "$root")/palomar-preflight" \
    "$root/palomar-preflight"; do
    [[ -n "$d" && -f "$d/palomar_preflight.sh" ]] && {
      cd "$d" && pwd
      return 0
    }
  done
  return 1
}

step() { printf '\n== %s ==\n' "$1"; }

cd "$ROOT"

step "Validate Comparator configuration"
python3 - <<'PY'
import json
with open("comparator.json", encoding="utf-8") as f:
    cfg = json.load(f)
required = ("challenge_module", "solution_module", "theorem_names", "permitted_axioms")
missing = [k for k in required if k not in cfg]
if missing:
    raise SystemExit(f"Missing comparator keys: {', '.join(missing)}")
if not cfg["theorem_names"]:
    print("NOTE: theorem_names empty; skipping chart audits")
else:
    names = cfg["theorem_names"] + cfg.get("definition_names", [])
    dup = sorted({n for n in names if names.count(n) > 1})
    if dup:
        raise SystemExit(f"Duplicate Comparator names: {', '.join(dup)}")
allowed = {"propext", "Quot.sound", "Classical.choice"}
bad = [a for a in cfg["permitted_axioms"] if a not in allowed]
if bad:
    raise SystemExit(f"Illegal permitted_axioms: {bad}")
print(f"OK: {len(cfg['theorem_names'])} theorems, "
      f"{len(cfg.get('definition_names', []))} definitions")
PY

if python3 -c 'import json; raise SystemExit(0 if json.load(open("comparator.json"))["theorem_names"] else 1)'; then
  step "Proof-chart axiom audit (all chart theorems)"
  bash scripts/validate_chart_axioms.sh
else
  step "Proof-chart axiom audit skipped (empty comparator chart)"
fi

# Build first: the type comparison reads the built Challenge/Solution oleans.
step "Build Lean project (ContinuousFOL + ContinuousFOLComparator Challenge/Solution)"
lake build

# Palomar/Verso rejects a Challenge or Solution module whose top-level name is
# also a top-level entry of a Lake dependency (e.g. a dependency that ships its own Challenge.lean).
step "Challenge/Solution module names vs Lake dependency top-level entries"
python3 scripts/check_module_name_clash.py

if python3 -c 'import json; raise SystemExit(0 if json.load(open("comparator.json"))["theorem_names"] else 1)'; then
  step "Compare Challenge/Solution declaration types"
  bash scripts/compare_challenge_solution_types.sh
else
  step "Challenge/Solution type compare skipped (empty comparator chart)"
fi

if toolkit="$(find_toolkit "$ROOT")"; then
  step "Shared palomar-preflight toolkit"
  SORRY_PATHS="ContinuousFOL ContinuousFOLComparator/Solution.lean"
  if bash "$toolkit/palomar_preflight.sh" --help 2>&1 | grep -q -- '--project-root'; then
    bash "$toolkit/palomar_preflight.sh" \
      --project-root "$ROOT" \
      --sorry-paths "$SORRY_PATHS" \
      "$@"
  else
    export PALOMAR_PROJECT_ROOT="$ROOT"
    export PALOMAR_SORRY_PATHS="$SORRY_PATHS"
    bash "$toolkit/palomar_preflight.sh" "$@"
  fi
else
  step "Shared toolkit not found (optional); local checks done"
fi

echo
echo "Palomar preflight finished."
