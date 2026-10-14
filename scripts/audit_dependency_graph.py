#!/usr/bin/env python3
"""Audit Lean imports independently of Lake's generated build graph.

The unrestricted theorem must have no dependency on retired
fixed-alphabet proof modules. The umbrella import should contain
no transitive duplicates. Optional public geometric modules may
be imported independently from the umbrella.
"""
from __future__ import annotations

from collections import defaultdict
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
RE = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", re.M)
sources = {p.relative_to(ROOT).with_suffix("").as_posix().replace("/", "."): p
           for p in (ROOT / "Milliken").rglob("*.lean")}
sources["Milliken"] = ROOT / "Milliken.lean"
graph = {}
for module, path in sources.items():
    src = path.read_text(encoding="utf-8")
    graph[module] = [i for i in RE.findall(src) if i in sources]


def reach(module: str) -> set[str]:
    found: set[str] = set()
    pending = [module]
    while pending:
        m = pending.pop()
        if m in found:
            continue
        found.add(m)
        pending.extend(graph.get(m, ()))
    return found


def path_between(start: str, goal: str) -> list[str] | None:
    seen = {start}
    q = [(start, [start])]
    for m, path in q:
        if m == goal:
            return path
        for child in graph.get(m, ()):
            if child not in seen:
                seen.add(child)
                q.append((child, path + [child]))
    return None


general = "Milliken.GeneralTree.HeterogeneousUniversalMilliken"
assert general in graph, f"Missing theorem module {general}"
closure = reach(general)
# Generic finite-colour consequences are no longer defined in Milliken.
assert "Milliken.FiniteColourRamseySpace" not in graph, ("Application-independent colour "
    "lemmas belong in RamseySpace.FiniteColouring")
assert "import RamseySpace.FiniteColouring" in (
    ROOT / "Milliken/GeneralTree/BaireColours.lean").read_text(), (
    "Tree-specific Baire corollary must use the shared RamseySpace module")
for old in (
    "Milliken.MillikenTheorem",
    "Milliken.Chapter6",
    "Milliken.HalpernLauchli.HalesJewettBridge",
    "Milliken.Applications.FiniteColour",
):
    if old in closure:
        route = path_between(general, old)
        raise SystemExit("FAIL: general theorem imports old homogeneous proof: " + " -> ".join(route or []))

for root in ["Milliken"]:
    direct = graph.get(root, [])
    redundant = sorted({x for x in direct
                        if any(x in reach(other) for other in direct if other != x)})
    print(f"{root}: {len(direct)} direct imports, {len(redundant)} transitively redundant")
    if redundant:
        raise SystemExit(f"FAIL: {root} has redundant imports: " + ", ".join(redundant))

print(f"PASS: {general} uses {len(closure)} local modules but does not import "
      "the homogeneous Milliken/Hales--Jewett proof; umbrellas are transitively minimal")

# The historical fixed-alphabet umbrella is intentionally removed.
if "Milliken.Applications" in graph:
    raise SystemExit("FAIL: legacy homogeneous umbrella still exists")
