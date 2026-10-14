# Milliken formalisation — mathematical, kernel, and API audit tracker

**Opened:** 14 October 2026  
**Frozen baseline:** `main` at `8bb11529b1631288954248eee6da53416d5b073e` (13 October 2026).  
**Documentation and original review:** merged as [PR #145](https://github.com/janhubicka/lean-milliken/pull/145). **Working code streams:** intrinsic finite extension (after merged #146); finite Baire colourings [#149](https://github.com/janhubicka/lean-milliken/pull/149); Galvin's alternative [#147](https://github.com/janhubicka/lean-milliken/pull/147).  
**Only supported client:** `janhubicka/lean-3-uniform-diaries` (ATR). No obligation to preserve historical `List ι` or `StrongEmbedding` wrappers.

This is a **living audit**, not a certificate that every assertion in the book or Milliken's 1979 article has been formalised. A green Lean build proves only the propositions actually elaborated. Each mathematical statement must also be compared with the source, including its finite/infinite object quantifiers.

## Auditable evidence

- Baseline GitHub Actions [run 38460157553](https://github.com/janhubicka/lean-milliken/actions/runs/38460157553): succeeded, including `lake build`, source-integrity scan, import-graph scan, and 523 designated `#print axioms` reports. The report checker allows only `propext`, `Classical.choice`, and `Quot.sound`.
- `scripts/audit_source_integrity.py` scans all library Lean files for local axioms and admissions. `scripts/audit_dependency_graph.py` tests that the unrestricted theorem does not reach the historical homogeneous proof.
- Existing independently *framed* referee analyses: `docs/audits/REFEREE_A_STATEMENT_SCOPE.md`, `REFEREE_B_PROOF_TRUST.md`, `REFEREE_C_DEPENDENCY_MINIMALITY.md`. These are **not external referee attestations**.
- Primary source examined: Todorčević, *Introduction to Ramsey Spaces* (2010), Chapter 3 and §6.1–6.2, especially printed pp. 135–140. [Scanned book](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf).
- Milliken, *A Ramsey theorem for trees*, *JCTA* **26** (1979), pp. 215–237, DOI [10.1016/0097-3165(79)90101-8](https://doi.org/10.1016/0097-3165(79)90101-8): the published abstract was checked. **The complete original article was not available for line-by-line verification**, so internal lemmas of that paper have not been certified.

## Status legend

- **VERIFIED-LEAN**: actual declaration inspected and baseline CI compiled/audited; note that this is not by itself a proof of source-equivalence.
- **MATCHED-SOURCE**: source statement/definition and Lean proposition compared in addition to compilation.
- **SCOPE-GAP**: formal theorem proves a nearby, potentially weaker property; an equivalence lemma is needed.
- **MISSING-EXPORT**: may follow from existing theorems but does not have a named checked result.
- **EXTERNAL/OPEN**: additional mathematics/application outside proved endpoints.
- **RECHECK AFTER CHANGE**: earlier green CI does not validate a later commit until that commit's own run succeeds.

## Work packages and exit conditions

| ID | Priority | Package | Current assessment | Exit condition |
| --- | --- | --- | --- | --- |
| P0-A | P0 | Source model: ambient, strongness, level restrictions | **MATCHED-SOURCE** for local finiteness, prunedness, ambient-successor uniqueness, optional off-root strong stem, source-level sequence; added `predecessor_exists` prevents ghost nodes | Record exact equivalence of formal strongness to intrinsic published (str1)–(str2), including restriction/gaps and root |
| P0-B | P0 | §6.1 (6.3), A.1–A.4, Ellentuck | **VERIFIED-LEAN / MATCHED-SOURCE**: unrestricted route uses literal `generalBookFinitization`, A.3, boundary A.4, genuine basic-neighbourhood topological conclusion | Check all imported abstract Ellentuck statement types and endpoints, no accidental choice of obsolete `leFin` |
| P0-C | P0 | Original 1979 finite-tree quantifiers | **PARTIAL, checked**: intrinsic finite witness, realised-to-intrinsic conversion, nonempty finite levels, unique finite root and bounded height all merged in [#146](https://github.com/janhubicka/lean-milliken/pull/146); reverse extension and equivalence still absent | Define intrinsic finite strong-tree type; prove extension to infinite strong tree and equivalence to realised finite approximation; restate corollary using intrinsic type |
| P0-D | P0 | Adversarial circularity/vacuity / kernel audit | **VERIFIED-LEAN** at pinned baseline. Universal HDHL induction quantified over *all* ambients and uses freshly built heterogeneous wedge | Rerun audit on final refactor commit; inspect all theorem-type parameters and transitive imports; record nontrivial test instances |
| P0-E | P0 | Sole client migration | **COMPLETE**: [Milliken #144](https://github.com/janhubicka/lean-milliken/pull/144) removed 81 historical homogeneous modules with successful CI; [ATR #395](https://github.com/janhubicka/lean-3-uniform-diaries/pull/395) removed corresponding wrappers and built against the reduced library | Pin updated successful upstream commit in ATR, pass both complete CIs, then merge in dependency-safe order |
| P1-A | P1 | Todorčević Lemma 6.1 and (6.4)–(6.8) | **VERIFIED-LEAN** for boundary cones, product HL, explicit strong graft and canonical A.4 | Check exact arbitrary-colour subset `O`, at depth `n`, and `n=0` case |
| P1-B | P1 | Corollaries 6.3–6.10 | **PARTIAL, VERIFIED-LEAN**: 6.4 Baire version merged as [#149](https://github.com/janhubicka/lean-milliken/pull/149); 6.7 realised Galvin alternative merged as [#150](https://github.com/janhubicka/lean-milliken/pull/150); 6.5 realised finite case proven; Souslin regularity, intrinsic finite equivalence and other corollaries remain | Enumerate each and implement direct natural corollaries without importing unrelated applications |
| P1-C | P1 | §6.2 Definitions 6.11, Lemma 6.12, Theorem 6.13, Cor. 6.14 | **EXTERNAL/OPEN** in this package: embedding-type/envelope applications are not automatically an interface consequence without definitions | Either formalise the mathematical transfer or explicitly mark this as beyond basic Milliken core |
| P1-D | P1 | Fixed-stem finite `Str_{ell,k}` | **VERIFIED-LEAN** for realised infinite refinements; **SCOPE-GAP** relative to intrinsic finite anchored objects | Prove finite restriction extension and the anchored all-intrinsic finite version (`ell ≤ k`) |
| P1-E | P1 | Synchronized *vector* Milliken | **EXTERNAL/OPEN**: `GeneralTree.Vector` declares target properties; level-product HL is strictly weaker than finite-vector-tree colouring | Prove vector theorem or show diary construction needs only scalar root-gluing and prove the appropriate transfer |
| P2-A | P2 | Lean implementation cleanup | 199 redundant umbrella imports and 81 historical modules removed; current supported code has no homogeneous proof import; remaining conditional proof stages retained when dependency-reachable | Reduce only proof-unreachable files / dead APIs, eliminate stale comments; all remaining imports reachable from supported public endpoints |
| P2-B | P2 | Researcher wiki and examples | **COMPLETE**: source documentation published under `docs/wiki/` and synchronized to the **actual** [GitHub Wiki](https://github.com/janhubicka/lean-milliken/wiki), including a sidebar; publishing [CI #38601106401](https://github.com/janhubicka/lean-milliken/actions/runs/38601106401) confirms a push to `.wiki.git` |
| P2-C | P2 | Long-term regression suite | **PARTIAL**: current general-tree CI includes a reduced endpoint-axiom audit, source-integrity and reachability scans, a nonvacuity regression; intrinsic-extension and full downstream semantics still need tests | Tests for level indexing, zero/positive-height cases, intrinsic finite extension, published order, downstream project CIs |

## Three adversarial review streams

**Referee A — statement semantics, attempted falsification.** Independently check that the formal class has the same members as the published `S_k(U)`, especially the difference between an *intrinsic* finite strong tree and a carrier accompanied by infinite extension. Test off-root trees, roots with one child, nonconstant/unbounded finite degrees, skipped ambient levels, and `k=0`. Check whether a hidden uniform degree bound or a fixed alphabet slips into the unrestricted endpoint.

**Referee B — proof dependency and kernel integrity.** Try to derive the alleged theorem from a stronger hidden premise by inspecting all final declaration arguments, looking for circular same-dimension HDHL, recursive calls on the wrong ambient, obsolete homogeneous imports, `sorry`, `axiom`, `constant`, unsafe compilation shortcuts, and #print-axioms output. Follow the negative somewhere-dense obstruction through compression and the wedge, not just positive density.

**Referee C — proof minimality and ATR migration.** Attempt to delete redundant exports/modules; challenge conditional bridges that can now be replaced with direct unconditional endpoints; check diary uses actual supported imports. Require green upstream *and* downstream CI before deleting old code.

No separate human referees have signed any of these streams. Work results and failed attempted counterexamples should be recorded with tested SHA and exact declarations.

## Stop/merge policy

1. Do **not** infer statement fidelity from green CI, nor claim all published corollaries are formalised because the main theorem compiles.
2. Propose code/deletion PRs separately from reference/wiki edits where possible.
3. Merge the upstream reduced library only after green complete CI at its latest head; update the one supported ATR dependency to the **same** SHA and obtain successful downstream CI.
4. Keep the `GeneralTree.Vector` target definitions as visibly unproved until a theorem inhabits them. Do not mislabel the product-level HL theorem as vector Milliken.
5. Record any actual mathematical correction as an explicit changed proposition or equivalence lemma, not only as prose.

## GitHub Wiki publication state — verified live

The documentation is published both in source-controlled
[`docs/wiki/README.md`](../wiki/README.md) **and** in the separate
[GitHub Wiki](https://github.com/janhubicka/lean-milliken/wiki).
The Wiki synchronization action
[`publish-wiki.yml`](../../.github/workflows/publish-wiki.yml)
successfully cloned the Wiki Git remote, generated `Home.md` from
`README.md`, and pushed the custom sidebar at Wiki commit `0771614`.
See [successful workflow run 38601106401](https://github.com/janhubicka/lean-milliken/actions/runs/38601106401).

Earlier initialization errors were resolved when the separate Wiki
repository became available. **No manual first-page step is outstanding.**
Future changes to source documentation trigger automatic Wiki updates.

## Active theorem tasks (after Wiki publication)

- [x] Intrinsic finite strong tree structure, finite frontier nonemptiness,
  first-level uniqueness and forward realised-to-intrinsic map: merged #146.
- [x] General-tree Baire-colouring refactor: merged #149 with green CI.
- [x] General-family realised Galvin alternative: merged #150 with green CI.
- [ ] Intrinsic finite-to-infinite completion: level continuation and full
  final-frontier cone geometry checked on [PR #151](https://github.com/janhubicka/lean-milliken/pull/151);
  genuine infinite strong-tree constructor and reverse equivalence
  remain open.
- [ ] Literal intrinsic 1979 finite-colour theorem and anchored finite
  corollaries, followed by additional §6.2 embedding-type applications.

## Immediate next steps

- [x] Capture baseline SHA and full CI evidence; inspect §6.1 and the original abstract.
- [x] Confirm the unrestricted theorem uses the *published* `bookLeFin`, not the old homogeneous shortcut.
- [x] Repair redundant umbrella import on PR #144.
- [x] Publish source-checked Chapter 3 and §6.1–6.2 statement matrix and human-readable proof architecture. Full 1979 paper line-by-line comparison remains unavailable.
- [x] Merge readable wiki navigation, proof/lemma guides and concise README in #145.
- [x] Merge upstream cleanup #144 and downstream ATR migration #395 after green head CIs.
- [x] Merge verified intrinsic finite strong-tree definition and forward map #146.\n- [ ] Prove intrinsic finite-to-infinite completion, its equivalence and literal 1979 statement.
- [ ] Verify §6.2 embedding-type transfer and whether it belongs in the supported API.
