# The Milliken tree theorem — Lean library wiki

This wiki documents the **verified unrestricted strong-subtree theorem** in `janhubicka/lean-milliken`. It is written for mathematicians and for the sole downstream client, `janhubicka/lean-3-uniform-diaries` (ATR). The library covers rooted trees with **finite nonempty immediate-successor sets**, with **no uniform bound** on their sizes. No homogeneous word alphabet is needed.

**Audit reference point:** `main` commit `8bb11529b1631288954248eee6da53416d5b073e`, whose [CI run](https://github.com/janhubicka/lean-milliken/actions/runs/38460157553) completed successfully (Lean build, source integrity, graph, designated kernel-axiom reports). The proposed ATR-only cleanup removes the historical fixed-alphabet proof and preserves the unrestricted theorem at [PR #144](https://github.com/janhubicka/lean-milliken/pull/144). Read the tracker before relying on future version numbers.

## Start here

| Page | Contents |
| --- | --- |
| **[Published statements](Published-statements.md)** | Precise correspondence to Todorčević §3 and §6.1–6.2, Milliken 1979 abstract, hypotheses, named Lean theorems, missing corollaries and mismatched finite-tree domains |
| **[Proof architecture](Proof-architecture.md)** | Mathematical explanation of the universal heterogeneous HDHL induction, full source-level compression, common-root wedge, complementary density transport, grafting, A.1–A.4 and Abstract Ellentuck |
| **[Geometry and auxiliary lemmas](Geometry-and-auxiliary-lemmas.md)** | Reusable nontrivial lemmas proved along the way: ranks, source fronts, finitisation, mixed protected graft, stabilization, matrices, wedge and code closedness |
| **[Adversarial referee record](Adversarial-referee-record.md)** | Three disjoint mathematical/kernel/maintainability challenges, verified facts, counterexample attempts and remaining proof obligations; never described as external peer-review signoff |
| **[ATR consumer and cleanup](ATR-consumer-and-cleanup.md)** | Single supported user, trim strategy, upstream/downstream CI requirement, exact scalar-vs-vector scope |
| **[Audit tracking](../audits/AUDIT_TRACKER_2026.md)** | P0/P1/P2 work packages, source version, acceptance tests, status and merge gates |

Older development notes remain in `docs/`; some were written when the unrestricted theorem was still conditional and must not override current theorem types.

## Principal checked endpoints

```lean
import Milliken.GeneralTree.UnconditionalHLAPI
import Milliken.GeneralTree.FixedStemUnconditional

#check Milliken.GeneralTree.heterogeneousHDHL_unconditional
#check Milliken.GeneralTree.generalProductHL_unconditional
#check Milliken.GeneralTree.boundaryProductHL_unconditional
#check Milliken.GeneralTree.generalPigeonhole_unconditional
#check Milliken.GeneralTree.generalMilliken_unconditional
#check Milliken.GeneralTree.milliken1979_general_unconditional
#check Milliken.GeneralTree.millikenFixedStemFiniteColouring_general
#check Milliken.GeneralTree.millikenFixedStemMonochromatic_general
```

The key topological endpoint is

```text
GeneralTree.generalMilliken_unconditional (U : AmbientTree) :
  RamseySpace.IsTopologicalRamseySpaceTextbook
    (S := GeneralTree.generalApproximationSystem U)
```

This is the actual *Baire-property and meagre-set* conclusion using published basic neighborhoods, not merely a finite Ramsey number or a conditional implication with HL assumed.

The 1979 finite-colour endpoint is **proved for `FiniteApprox U n`**, currently defined as prefixes having an infinite witness. The theorem is unconditional within that formal domain. **The identification with all intrinsic finite strong trees is an open documentation/definition-equivalence obligation**, and is a priority in the tracker.

## Modeling conventions

- Strong subtrees can have a root **strictly below the ambient root**.
- Each retained source level has a chosen **ambient height**, which may have arbitrarily large gaps.
- The next selected level meets each **ambient immediate-child cone exactly once**; weaker meet- or order-preserving subtrees are not interchangeable.
- `predecessor_exists` forbids “ghost” later selected nodes absent from the preceding frontier.
- `r 0 T` is empty. `r n T` keeps exactly the first `n` **source** levels.
- The full arbitrary-tree proof constructs A.2 using Todorčević’s `bookLeFin` with **maximal-level inclusion**. The old homogeneous `leFin` shortcut belongs to a distinct historical implementation.
- `GeneralTree.Vector` currently states synchronized finite-vector Milliken properties as **targets**, not as proved theorems. Monochromatic level products from HL are insufficient on their own to colour entire finite strong-tree vectors.

## Sources and verification

1. S. Todorčević, *Introduction to Ramsey Spaces* (2010), Chapter 3 (Halpern–Läuchli), Chapter 5 (Abstract Ellentuck) and Chapter 6 (strong subtree Ramsey space). [Book PDF](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf).
2. K. R. Milliken, *A Ramsey theorem for trees*, *Journal of Combinatorial Theory, Series A* **26** (1979), 215–237; [journal](https://doi.org/10.1016/0097-3165(79)90101-8). The published abstract has been checked; the full article is still required for any line-by-line audit of its detailed proof.
3. `lean-ramsey-space-todorcevic` pinned dependency, which contains the checked abstract Ellentuck theorem and a proof that its depth form is equivalent to the literal basic-neighbourhood version.

**What is proved vs not yet separately exported** is always specified on the [published-statements page](Published-statements.md). A whole-library successful `lake build` and `#print axioms` audit is excellent evidence for the stated Lean propositions, but not a substitute for checking the mathematical source-to-formal-domain correspondence.
