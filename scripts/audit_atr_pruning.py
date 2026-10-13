#!/usr/bin/env python3
"""Audit reachability from *all* arbitrary-tree modules.

ATR is the sole currently supported consumer; all GeneralTree modules,
the shared ambient and finite-colouring support are kept as roots. This
deliberately over-approximates ATR's dependency requirements.

A legacy module is safe to remove only when no retained GeneralTree or
ambient module imports it, transitively. The results are used as an
actionable list and are verified again after deletion.
"""
from collections import deque
from pathlib import Path
import re

root = Path(__file__).resolve().parents[1]
files = {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p
         for p in (root / "Milliken").rglob("*.lean")}
files["Milliken"] = root / "Milliken.lean"
pat = re.compile(r"^\s*import\s+([\w.]+)\s*$", re.M)
edges = {
    m: [x for x in pat.findall(path.read_text()) if x in files]
    for m, path in files.items()
}

roots = {m for m in files if m.startswith("Milliken.GeneralTree.")}
roots |= {
    "Milliken.AmbientTree", "Milliken.AmbientChild",
    "Milliken.FiniteColourRamseySpace",
}
roots &= set(files)
needed = set()
todo = list(roots)
while todo:
    m = todo.pop()
    if m in needed:
        continue
    needed.add(m)
    todo.extend(edges.get(m, []))

legacy = {m for m in files if m.startswith("Milliken.HalpernLauchli.")
          or m.startswith("Milliken.Applications.")
          or m in {"Milliken.Applications", "Milliken.MillikenTheorem",
                   "Milliken.Chapter6", "Milliken.Tree",
                   "Milliken.BranchEmbedding", "Milliken.Graft",
                   "Milliken.GraftRamsey"}}
legacy |= {
    m for m in files
    if m.count(".") == 1 and
    m not in {"Milliken", "Milliken.AmbientTree",
              "Milliken.AmbientChild", "Milliken.FiniteColourRamseySpace",
              "Milliken.GeneralTree"}
}

retain_legacy = sorted(legacy & needed)
prunable = sorted(legacy - needed)
print(f"All modules: {len(files)}, retained GeneralTree/ambient roots: {len(roots)}")
print(f"Reachable modules from general-tree interface: {len(needed)}")
print(f"Legacy files: {len(legacy)}; safely unused legacy files: {len(prunable)}")
if retain_legacy:
    print("LEGACY REACHABLE FROM GENERAL TREE (cannot blindly delete):")
    for item in retain_legacy:
        consumers = [a for a in needed if item in edges.get(a, ())]
        print(f"  {item} <- {', '.join(sorted(consumers))}")
else:
    print("PASS: unrestricted general-tree modules have no legacy homogeneous proof imports")
print("SAFE LEGACY CANDIDATES:")
for item in prunable:
    print("  " + str(files[item].relative_to(root)))

# The upstream proof must not rely on a homogeneous theorem implementation.
must_exclude = {
    "Milliken.MillikenTheorem", "Milliken.Chapter6",
    "Milliken.HalpernLauchli.HalesJewettBridge",
    "Milliken.Applications.FiniteColour",
}
if must_exclude & needed:
    raise SystemExit("FAIL: legacy homogeneous proof remains a general-tree dependency")
