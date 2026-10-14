# Adversarial referee record — three separate lines of attack

**Evidence baseline:** `main` at `8bb11529b1631288954248eee6da53416d5b073e`, whose [GitHub Actions](https://github.com/janhubicka/lean-milliken/actions/runs/38460157553) are green. The trimmed-library candidate `d2df3a15511c92f2bb4640a966c05aaae46147ab` also passed its [full CI](https://github.com/janhubicka/lean-milliken/actions/runs/38587255692). The audit was designed as three distinct adversarial reviews, **not** as attestations by separately recruited human referees.

## Referee A — mathematical semantics and source faithfulness

**Test:** Read Todorčević §6.1–6.2 and Milliken 1979's published abstract independently of the declaration names. Unfold every theorem's mathematical domain and codomain. Try unary trees, nonconstant local degree, large skipped ambient levels, roots above the ambient root, source height zero, and malformed carriers.

**A.1 Local branching — PASS.** The printed theorem assumes each node has finitely many but at least one immediate successor. `AmbientTree.finite_children` and `has_child` encode precisely this; the general theorem has no bounded-degree or fixed-alphabet hypothesis.

**A.2 Strongness — PASS with an essential extra field.** `StrongSubtree.successor_unique` represents *every ambient immediate-child cone* exactly once at the next source level. Without `StrongSubtree.predecessor_exists`, a proposed encoding permitted ghost nodes: in a binary tree, select levels 0,2,3,..., level-2 nodes 00 and 10, and also put 010 at level 3. The forward successor axioms alone would not reject that extra node, which has no level-2 selected ancestor. The current definition rejects it.

**A.3 Source/ambient rank — PASS.** `r n S` is defined using source level index `k<n`, not by ambient height `<n`. A gap from ambient level 0 to level 3 therefore does not erase the second source level.

**A.4 Printed finitisation — PASS in general proof; historical counterexample.** Todorčević's (6.3) is carrier inclusion **and** maximal-level inclusion. The old homogeneous `leFin` was different: for the unary identity tree, `a=r_1(id)` and `b=r_2(id)`, the old `leFin a b` holds but `bookLeFin a b` fails. The unrestricted proof correctly uses **`GeneralTree.generalBookFinitization` with literal `bookLeFin`**, including full A.2/A.3. Deletion of historical homogeneous code does not delete the book finitisation.

**A.5 Theorem 6.2 topology — PASS.** `generalMilliken_unconditional` concludes `IsTopologicalRamseySpaceTextbook`; the pinned Abstract Ellentuck library proves that it is the full basic-neighbourhood Baire/meagre formulation, equivalent to the internal depth version.

**A.6 1979 finite-tree quantifier — OPEN HIGH-PRIORITY GAP.** A `FiniteApprox U k` carries proof of an infinite realiser. Published `S_k(U)` quantifies over intrinsic finite strong subtrees. `exists_refinement_realising_general` transfers an **already realised** approximation into a target infinite subtree; it does **not** show every intrinsic finite strong tree can be realised. Needed: independent intrinsic structure, completion to infinite strong tree, equivalence (and relative containment inside `S`), and literal finite-colouring corollary. Until then, treat `milliken1979_general_unconditional` as *realised-form* rather than asserting an exact source-equivalent quantifier domain.

**A.7 Numbered applications — INCOMPLETE.** Todorčević Corollaries 6.6–6.10 and §6.2 Definition 6.11 / Lemma 6.12 / Theorem 6.13 / Corollary 6.14 are not all named Lean exports. Mark them individually missing; do not silently count them as kernel-checked because Theorem 6.2 is proved.

**A verdict:** unrestricted *topological* theorem matches the source; original intrinsic finite-tree and application coverage needs additional work.

## Referee B — kernel trust and circular dependencies

**Test:** Follow the complete final theorem's transitive import graph and actual proposition assumptions; challenge induction scope and complementary density transport. Audit admissions and `#print axioms` in CI.

**B.1 Proof integrity — PASS at pinned commits.** Main CI built the library and checked 523 designated endpoint axiom reports. `scripts/audit_source_integrity.py` scans all library Lean sources for local `axiom`, `constant`, `sorry`, `admit`. `check-axiom-log.py` rejects `sorryAx`, errors and unexpected axioms; its whitelist is only `propext`, `Classical.choice`, `Quot.sound`. The trimmed-code commit's CI also passed its adjusted full audits.

**B.2 No back door through old homogeneous theorem — PASS.** `scripts/audit_dependency_graph.py` rejects general theorem imports reaching historical `MillikenTheorem`, `Chapter6`, homogeneous `HalesJewettBridge` and `Applications.FiniteColour`. The generic Baire-colouring bridge has been moved to the upstream `RamseySpace.FiniteColouring` library; the general theorem remains independent of historical fixed-alphabet proofs.

**B.3 Legitimate induction over a changed ambient — PASS.** `universalHeterogeneousHDHL` quantifies over every ambient tree, and explicitly specializes its previous-dimensional hypothesis to the newly built wedge. An induction fixed to the input tree `U` would not suffice.

**B.4 Negative matrix transport — PASS at inspected proof types.** `no_wedge_complement_somewhereDense` is actually used before the reduced density theorem. This converts a hypothetical complementary matrix in the wedge into a forbidden *restricted* original matrix; aligning distinct base levels to one penultimate rank is essential. Positive-density transfer alone would not justify the result.

**B.5 Non-vacuity regression recommended.** Since each source-level product is nonempty and `HeterogeneousMatrix.fullLevel P n` is dense at `n`, the empty set cannot satisfy `HeterogeneousHighlyDense P ∅`. A direct kernel-checked lemma is a useful test that the density hypothesis is not accidentally vacuous.

**B.6 Conditional means conditional.** Several `..._of_HL` and `..._of_previous` statements take an explicit stronger premise. They are not used as axioms: the final path supplies these premises with the universal unconditional HDHL proof. Check the **final type**, not a suggestive theorem name.

**B verdict:** proof trust and dependency separation pass at pinned CI versions. Mathematical source fidelity remains Referee A's separate obligation.

## Referee C — library minimality and reusability

**Test:** Challenge every import, compatibility wrapper and duplicate final theorem. Delete code only after proof-reachability analysis, while preserving a readable and compositional mathematical API.

**C.1 199 redundant umbrella imports — REMOVED.** Prior merged PR #143 reduced the direct umbrella imports from 87/131 to 9/10, preserving the transitive import closure.

**C.2 81 historical homogeneous modules — CLEANUP CI PASSED.** [Milliken PR #144](https://github.com/janhubicka/lean-milliken/pull/144) deletes the separate `StrongEmbedding` / Hales–Jewett / homogeneous Chapter 6 implementation and preserves general-tree theorem dependencies. It extracts an old source-index enumerator into `GeneralTree.IncreasingEnumeration`. A redundant `Vector` umbrella import caused an initial non-proof graph failure, fixed in `d2df3a15`. The full upstream workflow then passed.

**C.3 Public API and downstream integration — PASS for the core library.** The earlier fixed-alphabet compatibility layer was deleted, and independent downstream integration builds verified that the retained general-tree interfaces suffice. Future clients should pin tested revisions; the mathematical API should remain application-neutral rather than importing domain-specific coding structures.

**C.4 Avoid dangerous over-pruning.** `GeneralTree/BoundaryMilliken`, `Original1979Conditional`, `CanonicalPigeonhole`, `HeterogeneousReducedInduction`, wedge and protected-fusion modules are meaningful checked decomposition steps, not necessarily obsolete because there is a later unconditional theorem. Dead files should be defined by import reachability and actual downstream imports, not by their date.

**C.5 Scalar-versus-vector obstruction.** `HasVectorMillikenFiniteColourProperty` is still a *definition*, not a theorem. A three-coordinate level-product Halpern–Läuchli theorem does not colour all finite synchronized **vector strong-subtree** shapes. Some applications may transfer via scalar root-gluing, but their realization and decoding obligations must be proved in the application. Library cleanup must not hide them.

**C verdict:** API reduction is mathematically acceptable with downstream CI and an explicit vector/scalar scope statement.

## Regression priorities

| Priority | Challenge | Acceptance |
| --- | --- | --- |
| P0 | Intrinsic finite strong subtree extends to infinite realization | New Lean theorem with no hidden existing-realization field |
| P0 | A finite strong subtree *of* S versus a U-strong subtree whose carrier is inside S | Exact equivalence/containment bridge for 1979 output |
| P0 | Reusable public imports and downstream interoperability | Green `lake build`, complete axiom/integrity checks, and a separately checked example downstream project |
| P1 | Highly dense empty-set impossibility | Lean non-vacuity lemma using `fullLevel_denseAt` |
| P1 | Boundary graft at stem length zero | Regression theorem matching root cone case |
| P1 | Independently named Corollaries 6.6–6.10 and §6.2 transfer | Each statement genuinely elaborates rather than appears only in prose |
| P2 | Dead declarations and stale “still unproved” comments | Minimal supported root import graph, clear current module docs |

**No external mathematical referee certification is claimed here.** This is the reproducible adversarial-review dossier, to be extended with actual failing Lean examples and tested SHAs as later phases proceed. For the phase schedule consult [the audit tracker](../audits/AUDIT_TRACKER_2026.md).
