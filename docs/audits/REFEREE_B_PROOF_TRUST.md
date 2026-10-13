# Adversarial referee B — proof trust and verification

Reviewed: the `lakefile.toml` pinning, GitHub Actions workflow,
`scripts/CheckMilliken.lean`,
`scripts/check-axiom-log.py`, the common-ambient wedge and
unconditional HDHL theorem interfaces.

This is an independently focused proof-trust audit pass, **not** an
external human reviewer certificate.

## Positive evidence

- The existing CI first runs `lake build` and separately executes
  `#print axioms` on **523 designated endpoints**.
- `scripts/check-axiom-log.py` rejects any report with `sorryAx`,
  unexpected axioms, or a wrong number of proof reports.
- The explicit whitelist is just `propext`, `Classical.choice`,
  and `Quot.sound`.
- The general-tree induction is quantified over every ambient rather
  than silently reusing the old ambient after compression.

## Adversarial tests added in the audit branch

1. `scripts/audit_dependency_graph.py` recursively checks the **actual
   imports** of the new universal heterogeneous theorem and rejects a
   transitive route through the separate homogeneous
   `MillikenTheorem`/`HalesJewettBridge` proof.
2. `scripts/audit_source_integrity.py` checks **all** Lean library
   source files for `sorry`, `admit`, `sorryAx` and locally introduced
   `axiom` or `constant`, excluding nested comments and strings.
   This closes a gap in the endpoint-only axiom audit.
3. `lake build` still checks the unchanged historical homogeneous
   theorem, while the general theorem must now compile through the
   generic abstract Ramsey-space finite-colouring lemma alone.

## Limitations

A successful Lean axiom audit does not by itself certify that the
formal statement exactly matches a published informal statement.
The independent mathematical audit addresses the
intrinsic/realised finite-tree distinction and the source-level
interpretation. Likewise, a textual integrity scanner is supplementary
to Lean's kernel, not a substitute for proof-term verification.

**Assessment:** Trust setup is good for audited theorem statements.
The new CI isolation check and all-source scan make the evidence
stronger and protect future refactors.
