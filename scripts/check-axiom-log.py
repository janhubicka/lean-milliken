#!/usr/bin/env python3
"""Reject admitted or nonstandard axioms in Lean #print axioms output."""
from __future__ import annotations

from pathlib import Path
import re
import sys

if len(sys.argv) != 3:
    raise SystemExit("usage: check-axiom-log.py LOG EXPECTED")

path = Path(sys.argv[1])
expected = int(sys.argv[2])
text = path.read_text(encoding="utf-8")

if "sorryAx" in text or re.search(r"\berror:", text):
    raise SystemExit("FAIL: error or admitted proof in axiom report")

reports = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text, re.S)
reports += [""] * len(re.findall(r"does not depend on any axioms", text))

if len(reports) != expected:
    raise SystemExit(
        f"FAIL: expected {expected} axiom reports, received {len(reports)}"
    )

allowed = {"propext", "Classical.choice", "Quot.sound"}
for report in reports:
    actual = {x.strip() for x in report.split(",") if x.strip()}
    extra = actual - allowed
    if extra:
        raise SystemExit(f"FAIL: unexpected proof axioms: {sorted(extra)}")

print(f"PASS: {len(reports)} reports use only standard Lean axioms")
