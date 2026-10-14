# lean-milliken

Lean 4 formalisation of **Milliken's tree theorem** for strong subtrees of
**arbitrary rooted pruned locally finitely branching trees**. Node degrees can
vary and need not be bounded over the tree. The proof follows Todorčević's
*Introduction to Ramsey Spaces* (Chapters 3, 5 and 6) and derives the full
topological Ramsey-space conclusion through the verified Abstract Ellentuck
theorem. There is no homogeneous-alphabet assumption in the exported general
result.

## Start with the [researcher wiki](docs/wiki/README.md)

- [Published theorem crosswalk](docs/wiki/Published-statements.md): exact
  comparison of Todorčević §3, §6.1–6.2, and the abstract of Milliken (1979);
  explicit coverage status for Corollaries 6.3–6.14.
- [Human-readable complete proof](docs/wiki/Proof-architecture.md): heterogeneous
  Halpern–Läuchli, source-level compression, common-root wedge, negative
  obstruction transport, synchronized grafting, A.1–A.4 and Abstract Ellentuck.
- [Auxiliary lemma index](docs/wiki/Geometry-and-auxiliary-lemmas.md):
  mathematical meaning and locations of the nontrivial supporting lemmas.
- [Adversarial review](docs/wiki/Adversarial-referee-record.md):
  three distinct statement, proof and minimality checks, failed counterexamples
  and remaining scope gaps.
- [Audit tracker](docs/audits/AUDIT_TRACKER_2026.md): pinned CI and work packages.
- [Sole client: three-uniform diaries](docs/wiki/ATR-consumer-and-cleanup.md):
  supported API and migration away from obsolete homogeneous modules.

Historical chronological development notes are retained under `docs/`, but
the wiki and current theorem types take precedence over outdated “open” labels.

## Use the unrestricted theorem

```lean
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

#check Milliken.AmbientTree
#check Milliken.GeneralTree.generalApproximationSystem
#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.generalProductHL_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.milliken1979_general_unconditional
#check Milliken.GeneralTree.millikenFixedStemFiniteColouring_general
#check Milliken.GeneralTree.millikenFixedStemMonochromatic_general
```

The central theorem `generalMilliken_unconditional U` has result type
`RamseySpace.IsTopologicalRamseySpaceTextbook (S := generalApproximationSystem U)`.
It proves the **Baire-set Ramsey and meagre-set Ramsey-null** properties in the
literal basic-neighbourhood formulation. It is not merely a conditional theorem
assuming Halpern–Läuchli, and not merely a finite-colouring consequence.

The proof is organised as

```text
  all-dimensional heterogeneous highly-dense Halpern–Läuchli
      → synchronized finite-colour product Halpern–Läuchli
      → boundary-cone one-step pigeonhole
      → published A.4 (with A.1–A.3 and closedness)
      → Abstract Ellentuck → unrestricted topological Milliken
      → finite-colour and protected-stem consequences
```

The central implementation `Milliken/GeneralTree/HeterogeneousUniversalMilliken.lean`
proves HDHL by universal induction over all ambient trees. It uses *full*
compression at selected **source indices** and a common-root wedge to give
different coordinate trees one synchronized ambient. Negative
somewhere-dense obstruction transport is checked explicitly.

### Conventions

A `StrongSubtree U` can start below the root of `U`. Every retained source
level has a chosen ambient height, possibly with large gaps. Every immediate
**ambient** successor cone has precisely one descendant at the next selected
source level. The `predecessor_exists` condition prevents extraneous
“ghost” selected nodes. `r n T` consists of the first `n` selected source
levels, with `r 0 T = ∅`.

A.2 uses the **literal published** finitisation `bookLeFin`, including
maximal-level inclusion, not the old homogeneous carrier-only shortcut.
The source-level geometry and the Abstract Ellentuck theorem are separate
verified Lean dependencies; both have exact theorem interfaces.

### Important limits

The original 1979 paper and Todorčević Corollary 6.5 colour **all intrinsic
finite strong subtrees**. The current unconditional theorem
`milliken1979_general_unconditional` is stated for `FiniteApprox U k`,
which includes an **infinite-realisation witness**. The separate proof that
every intrinsic finite strong tree has such a witness, and the type/colouring
equivalence, is a priority in the [audit tracker](docs/audits/AUDIT_TRACKER_2026.md).
We do not claim literal 1979 source-equivalence until this bridge is checked.

The finite **synchronized vector strong-subtree** colouring property in
`GeneralTree.Vector` remains a *target proposition*, not a proved theorem.
Heterogeneous level-product Halpern–Läuchli is a different, already verified
result. Three-uniform diaries can use the scalar theorem after an explicit,
checked root-gluing and decoding/realisation transfer.

Some numbered applications of Todorčević §6.1–6.2 do not yet have individual
named Lean exports; see the [crosswalk](docs/wiki/Published-statements.md).

## Reproduce kernel checks

The main-branch snapshot at `8bb11529b1631288954248eee6da53416d5b073e`
passed [GitHub Actions run 38460157553](https://github.com/janhubicka/lean-milliken/actions/runs/38460157553):
full `lake build`, dependency-graph and source-integrity checks, and 523
designated `#print axioms` reports. The axiom checker permits only
`propext`, `Classical.choice`, `Quot.sound`.

```bash
lake update
lake exe cache get
lake build
python3 scripts/audit_dependency_graph.py
python3 scripts/audit_source_integrity.py
lake env lean scripts/CheckMilliken.lean > proof-audit.log 2>&1
# See .github/workflows/lean.yml for the pinned expected report count.
```

The [ATR-only cleanup PR #144](https://github.com/janhubicka/lean-milliken/pull/144)
removes 81 unused fixed-alphabet historical modules. Its updated revision
`d2df3a15511c92f2bb4640a966c05aaae46147ab` passed [complete CI](https://github.com/janhubicka/lean-milliken/actions/runs/38587255692).
The only supported downstream consumer is
[janhubicka/lean-3-uniform-diaries](https://github.com/janhubicka/lean-3-uniform-diaries);
compatibility wrappers no longer required there should not constrain this API.

## References

- S. Todorčević, *Introduction to Ramsey Spaces*, Princeton University Press,
  2010, especially §3.1–3.2, §5.1, §6.1–6.2.
  [Full book](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf).
- K. R. Milliken, “A Ramsey theorem for trees,” *J. Combin. Theory Ser. A*
  **26** (1979), 215–237.
  [DOI](https://doi.org/10.1016/0097-3165(79)90101-8).
