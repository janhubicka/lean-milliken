# Milliken's theorem — Lean research library

This wiki documents a verified Lean 4 development of the strong-subtree
Milliken theorem for arbitrary **pruned, rooted, locally finitely branching**
trees. The branching degree can depend on each node and be unbounded
over the full tree.

The intended readers are mathematicians using the library to formalise
new Ramsey-theoretic statements, and researchers comparing the
formal proof with Todorčević's *Introduction to Ramsey Spaces* and
Milliken's original paper.

## Read the library

| Chapter | Content |
| --- | --- |
| **[Using the library](Using-the-library.md)** | Install with Lake, import the public theorems, examine assumptions, compose reusable lemmas and build downstream tests |
| **[Published statements](Published-statements.md)** | Source-faithful map of theorems in Chapters 3, 5 and 6; distinction between checked results, corollaries and outstanding formal equivalents |
| **[Proof architecture](Proof-architecture.md)** | Detailed human-readable heterogeneous HDHL induction, selected-level compression, common-root wedge, positive and negative matrix transfer, A.1–A.4 and Abstract Ellentuck |
| **[Geometry and auxiliary lemmas](Geometry-and-auxiliary-lemmas.md)** | Strongness, ranks, protected grafting, finitisation, boundary cones, stabilization, compression, matrix transports and closedness |
| **[Intrinsic finite completion](Intrinsic-finite-completion.md)** | Intrinsic strong finite trees versus realised approximations; constructive extension argument and current Lean proof status |
| **[Adversarial referee audit](Adversarial-referee-record.md)** | Mathematical statement fidelity, kernel/dependency trust, and minimality audits; explicit gaps and attempted counterexamples |
| **[Audit tracker](../audits/AUDIT_TRACKER_2026.md)** | Pinned CI results, unfinished proof obligations and regression criteria |
| **[Wiki publishing](Publishing.md)** | How source-controlled documentation is synchronized to this GitHub Wiki |

The source of truth is the version-controlled `docs/wiki/` directory.
Changes to those files automatically publish to the [GitHub Wiki](https://github.com/janhubicka/lean-milliken/wiki).

## Main theorem endpoints

```lean
import Milliken

#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.generalProductHL_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.heterogeneousHDHL_unconditional
#check Milliken.GeneralTree.milliken1979_general_unconditional
#check Milliken.GeneralTree.millikenFixedStemFiniteColouring_general
#check Milliken.GeneralTree.millikenFiniteBaireColouring
#check Milliken.GeneralTree.galvinAlternative_realized
#check Milliken.GeneralTree.exists_refinement_realising_with_stem

-- Generic finite-colour lemmas for any topological Ramsey space.
#check RamseySpace.finiteBaireColouring
#check RamseySpace.finiteApproximationColouring
```

The central theorem concludes
`RamseySpace.IsTopologicalRamseySpaceTextbook` for the approximation
system `generalApproximationSystem U`. Thus it gives both the
Ramsey property of all Baire sets and Ramsey-nullity of all meagre
sets in genuine basic neighbourhoods; it is not a conditional
Halpern–Läuchli implication.

## Definitions worth checking

A strong subtree has one strictly increasing sequence of selected
ambient levels, may start below the ambient root, and meets every
immediate ambient child cone of a selected node in exactly one node
at the next selected source level. The finite restriction `r n S`
keeps precisely the first `n` source levels. Todorčević's published
`bookLeFin` includes both carrier and maximal-level inclusion.

The present 1979-style finite-colouring API quantifies over *realised*
finite approximations. The exact intrinsic finite-tree equivalence
requires the separately documented reverse extension lemma.
Similarly, products of synchronized **level nodes** and synchronized
**finite strong-subtree vectors** are different objects and must not
be conflated.

## Verification

The repository workflow builds all Lean modules, scans all
source files for unsound admissions, checks the theorem-axiom
reports, and audits import dependencies. These checks establish
proof integrity for the actual elaborated statements; the
mathematical correspondence with printed statements is reviewed
independently in the audit chapters.

Sources: S. Todorčević, *Introduction to Ramsey Spaces* (2010),
Chapters 3, 5, 6; K. R. Milliken, *A Ramsey theorem for trees*,
*J. Combinatorial Theory A* **26** (1979), 215–237.
