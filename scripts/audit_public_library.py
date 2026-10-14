#!/usr/bin/env python3
"""Guard the Milliken library's application-neutral public interface.

No domain-specific research project belongs in the theorem library's
module names, source comments, README, wiki or audit scripts. Project
integrations belong in their respective downstream repositories.

The regex patterns are composed here so that the scan does not report
its own source as containing prohibited phrases.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
IGNORED_DIRS = {".git", ".lake", "__pycache__", ".venv"}
SUFFIXES = {".lean", ".md", ".py", ".toml", ".yml", ".yaml"}
PROJECT_TOKENS = (
    "A" + "T" + "R",
    "di" + "aries",
    "three" + "-uniform",
    "3" + "-uniform",
)
EXCLUDED = {Path("scripts/audit_public_library.py")}

problems: list[str] = []
checked = 0
for path in sorted(ROOT.rglob("*")):
    if not path.is_file() or path.suffix not in SUFFIXES:
        continue
    rel = path.relative_to(ROOT)
    if rel in EXCLUDED or any(part in IGNORED_DIRS for part in rel.parts):
        continue
    checked += 1
    path_text = rel.as_posix().casefold()
    for token in PROJECT_TOKENS:
        if token.casefold() in path_text:
            problems.append(f"{rel}: application-specific file name: {token}")
    text = path.read_text(encoding="utf-8")
    for lineno, line in enumerate(text.splitlines(), start=1):
        for token in PROJECT_TOKENS:
            pat = (r"\b" + re.escape(token) + r"\b"
                   if token.isalpha() and len(token) <= 3
                   else re.escape(token))
            if re.search(pat, line, flags=re.IGNORECASE):
                problems.append(f"{rel}:{lineno}: application-specific reference ({token})")

if problems:
    raise SystemExit(
        "FAIL: Milliken is a reusable theorem library; application-specific "
        "references must live downstream:\n" + "\n".join(problems)
    )
print(f"PASS: {checked} source/documentation files are application-neutral")
