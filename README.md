# lean-milliken

A Lean 4 development of Milliken's theorem for **strong subtrees**, following
Stevo Todorčević, *Introduction to Ramsey Spaces*, Chapter 6, and
Keith R. Milliken, *A Ramsey theorem for trees* (1979). The main homogeneous
tree theorem is derived from the checked infinite Hales–Jewett theorem and the
Abstract Ellentuck theorem. The library also provides finite-colouring and
fixed-stem interfaces for applications.

**Scope and verification:** The unconditional theorem is currently for a
**homogeneous** ambient tree `List ι`, where `ι` is a finite nonempty
alphabet. The **main branch** also includes a source-facing API for
**arbitrary pruned, finitely branching rooted trees**. This is a checked
collection of definitions and elementary lemmas; the unrestricted
general-tree Ramsey theorem is **not yet proved**. Do not confuse a
proposition stating that theorem with its proof.

The selected-level geometry with increasing branching and the application
API were merged in [PR #3](https://github.com/janhubicka/lean-milliken/pull/3)
and [PR #4](https://github.com/janhubicka/lean-milliken/pull/4).
Both their branches and the combined main revision passed Lean CI.
The full selected-level induction and arbitrary node-dependent branching
transfer remain open.

## Quick start

Pin the library revision in your downstream Lake package. For the
homogeneous theorem and applications, import:

```lean
import Milliken.Applications

#check Milliken.Chapter6.milliken
#check Milliken.Chapter6.milliken_onBasicNeighborhoods
#check Milliken.Applications.todorcevic62_homogeneous
#check Milliken.Applications.millikenFiniteColouring
#check Milliken.Applications.millikenFixedStemFiniteColouring
#check Milliken.Applications.milliken1979_homogeneous
#check Milliken.Applications.millikenFixedStem1979_homogeneous
```

For the definitions for a general ambient tree, use
`import Milliken.GeneralTree.Published`:

```lean
import Milliken.GeneralTree.Published

#check Milliken.AmbientTree
#check Milliken.GeneralTree.StrongSubtree
#check Milliken.GeneralTree.FiniteApprox
#check Milliken.GeneralTree.SInfinity
#check Milliken.GeneralTree.SFinite
#check Milliken.GeneralTree.r
#check Milliken.GeneralTree.maxLevel
#check Milliken.GeneralTree.bookLeFin
#check Milliken.GeneralTree.BasicNeighborhood
#check Milliken.GeneralTree.HasMillikenFiniteColourProperty
```

The last declaration is a **`Prop` describing an unproved target**, not
an axiom, typeclass instance, or theorem. The complete implementation,
including the separate Chapter 3 reconstruction, is available with
`import Milliken`.

### Conventions (important for applications)

* A tree is rooted, **finitely branching at each node**, and of height
  at most `ω`. For the infinite Ramsey theorem it has height `ω` and
  **no terminal nodes**. The number of children can depend on the node
  and can be unbounded over the tree.
* A strong subtree need **not** contain the root of its ambient tree.
* Its selected levels form a strictly increasing sequence of **ambient
  levels**. A source level `n` is generally **not** ambient level `n`.
* A finite tree of height `k` consists of source levels
  `0, …, k−1`. The height-zero approximation is empty.
* A strong subtree must account for **every immediate successor in
  the ambient tree**: each successor cone has **exactly one**
  representative at the next selected level. An arbitrary
  meet-preserving or weak subtree is not enough.
* For an anchored statement `r_ell(B)=r_ell(A)` means equality of
  the first `ell` **source** levels, not equality of ambient truncations
  at level `ell`.

## 1. Arbitrary ambient trees — published-source data model

Namespace: `Milliken` and `Milliken.GeneralTree`.
Modules: [`AmbientTree.lean`](Milliken/AmbientTree.lean),
[`GeneralTree.lean`](Milliken/GeneralTree.lean),
[`GeneralTree/Published.lean`](Milliken/GeneralTree/Published.lean).

| Declaration | Meaning and hypotheses |
| --- | --- |
| `AmbientTree` | A Mathlib `RootedTree` together with `finite_children : ∀ x, (children x).Finite` and `has_child : ∀ x, ∃ y, x ⋖ y`. Thus the branching is locally finite and the tree has no leaves. |
| `AmbientTree.children U x` | Set of **immediate ambient successors** `{y : U \| x ⋖ y}`. |
| `AmbientTree.children_finite`, `children_nonempty` | The two main structural hypotheses exported as lemmas. |
| `AmbientTree.level U x`, `levelSet U n` | Ambient height above the root and the set of nodes at ambient level `n`. |
| `GeneralTree.StrongSubtree U` | Infinite strong subtree represented by its **carrier**, strictly increasing selected ambient levels, a selected root, ancestral closure and the ambient-successor uniqueness property. |
| `StrongSubtree.sourceLevel S n` | `S` at its `n`th selected level. `sourceLevel_nonempty` establishes nonemptiness. |
| `StrongSubtree.initialPart S n` | First `n` source levels, the book's `T ↾ n`. `initialPart_zero`, `initialPart_mono`, `initialPart_subset` describe truncation. |
| `StrongSubtree.Refines S T` | Strong-subtree inclusion `S.carrier ⊆ T.carrier`, with both objects strong in the same ambient `U`. |
| `GeneralTree.FiniteApprox U n` | A finite approximation of source height `n`, stored as a carrier together with a witness that it is the first `n` levels of some infinite strong subtree. |
| `GeneralTree.approx n S` | Restriction to the first `n` source levels, keeping the realizer. |
| `GeneralTree.SInfinity U`, `SFinite U n` | Book-facing aliases for `S_∞(U)` and `S_n(U)` (with finite approximations represented by infinite realizers). |
| `GeneralTree.r n S` | Source-facing alias for `r_n(S)=S↾n`, formula (6.1). |
| `GeneralTree.maxLevel a` | The set of maximal nodes of finite approximation `a` in its **induced tree order**, i.e. `a(max)`. |
| `GeneralTree.bookLeFin a b` | Literal (6.3): both carriers empty, **or** `a.carrier ⊆ b.carrier` and `maxLevel a ⊆ maxLevel b`. |
| `GeneralTree.BasicNeighborhood a T` | `[a,T]`: strong refinements `S ⊆ T` with `r_n(S)=a`, where `a` has height `n`. |
| `GeneralTree.HasMillikenFiniteColourProperty U` | **Unproved target** for the original general-tree theorem: every finite colouring of height-`n` approximations has a monochromatic infinite strong subtree of `U`. |

The fields of `GeneralTree.StrongSubtree U` are intentionally more explicit
than the printed (str1)–(str2). `root_mem`/`root_below` make the induced
subtree rooted; `carrier_levels` expresses regularity;
`successor_unique` is **(str2)** quantified over all immediate successors
in `U`, while `predecessor_exists` prevents nodes at a later selected
level that do not descend from any node of the preceding selected level.
Otherwise a “ghost” node could satisfy the forward successor condition
without being part of a regular rooted strong subtree. The chosen root can
lie strictly above the root of `U`.

**Important modeling distinction:** `FiniteApprox U n` currently requires
an infinite realizer. This represents the approximations used by the
Ramsey-space construction. To identify it with the *intrinsic* class
of all finite strong subtrees in `S_n(U)` without that witness, prove a
finite-strong-subtree extension lemma. The arbitrary-tree topological
Ramsey-space instance, its A.1–A.4 proof and that identification are
not exported as proved results yet.

## 2. Homogeneous strong-tree API (proved core)

Namespace: `Milliken`, `Milliken.StrongEmbedding` and
`Milliken.StrongTreeSpace`.

| Declaration | Description |
| --- | --- |
| `Node ι`, `child s i` | Nodes are finite words `List ι`; a labelled child is `s ++ [i]`. |
| `StrongEmbedding ι` | Canonical embedding of the full homogeneous tree into itself, with `toFun`, injectivity, prefix preservation/reflection, branch preservation/reflection and a strictly increasing common level map. **Root not fixed.** |
| `StrongEmbedding.id`, `comp`, `comp_assoc` | Identity, composition and associativity of strong embeddings. |
| `StrongEmbedding.range F` | Node carrier of the embedded strong subtree. |
| `StrongTreeSpace.le ι X Y` | Refinement/factorisation: `∃ Z, X = Y.comp Z`. |
| `StrongTreeSpace.le_iff_range_subset` | Equivalent to inclusion of strong-subtree node carriers, assuming `[Nonempty ι]`. |
| `StrongTreeSpace.FiniteNode ι n` | Words of source length **strictly less** than `n`. |
| `StrongTreeSpace.Approx ι n` | A restriction of a strong embedding to its first `n` source levels, with a realisation witness. |
| `StrongTreeSpace.approx ι n X` | The restriction `r_n(X)`; `approx_surjective`, `approx_zero`, `coherent`, `separated` prove basic A.1 properties. |
| `StrongTreeSpace.approxCarrier a` | The image nodes of a finite approximation. |
| `StrongTreeSpace.approxMaxLevel a` | The image of its last source level, empty for height zero. |
| `StrongTreeSpace.bookLeFin a b` | Source-facing **(6.3)** maximal-level order. An empty first approximation is below any target (`bookLeFin_of_zero`); reflexivity is `bookLeFin_refl`. |
| `StrongTreeSpace.leFin a b` | Alternative order used **internally** by the checked Chapter 6 A.2/A.3/A.4 construction: height inequality and carrier inclusion. |
| `StrongTreeSpace.stemExtension`, `approx_comp_stemExtension` | Extend a finite strong stem lying in an infinite strong subtree and realize it by a further strong embedding. |
| `StrongTreeSpace.finitization` | Checked A.2 witness **for `leFin`**, not yet an A.2 witness for `bookLeFin`. |
| `StrongTreeSpace.amalgamation_nonempty`, `amalgamation_refine` | Checked A.3 nonempty and refinement instances. |
| `StrongTreeSpace.isMetricallyClosed`, `isTychonoffClosed` | The approximation-code image is closed, allowing Abstract Ellentuck. |

**Finitisation caveat:** `leFin` and `bookLeFin` are **not identical
binary relations**. For example `r_1(id) ≤fin r_2(id)` holds for
`leFin` but fails for `bookLeFin`: the top levels differ. The test
`comparison_leFin` / `comparison_not_bookLeFin` is in
[`FinitizationComparison.lean`](Milliken/Applications/FinitizationComparison.lean).
The A.1–A.4 development is Lean-checked for `leFin`. To claim literal
identity with Todorčević's topology, the relevant **depth and
basic-neighbourhood equivalence** must additionally be verified. The
public `bookLeFin` definition is supplied for that comparison.

## 3. Unconditional theorem exports

Modules: [`MillikenTheorem.lean`](Milliken/MillikenTheorem.lean),
[`Applications`](Milliken/Applications.lean).

All listed unconditional homogeneous theorems assume a finite nonempty
branching alphabet `ι`. Finite-colouring corollaries take a colour type
`κ` with `[Fintype κ]`.

| Declaration | What it proves |
| --- | --- |
| `Milliken.HalpernLauchli.HalesJewettBridge.strongSubtreeHL` | The full finite-dimensional strong-subtree Halpern–Läuchli property on a product of homogeneous trees: **one common selected level map** and monochromatic level products, via Hales–Jewett. |
| `Milliken.Chapter6.abstractRamseySpace` | The A.1–A.4 structure for the homogeneous approximation system, assembled from the internal finitisation, amalgamation and pigeonhole lemmas. |
| `Milliken.Chapter6.milliken` | The full topological Ramsey-space conclusion `RamseySpace.IsTopologicalRamseySpace` for that structure. |
| `Milliken.Chapter6.milliken_onBasicNeighborhoods` | Source-facing result on **all** basic Ellentuck neighbourhoods (`IsTopologicalRamseySpaceOnBasicNeighborhoods`). |
| `Milliken.Applications.todorcevic62_homogeneous` | Alias for Theorem 6.2 restricted to homogeneous ambient trees and the checked approximation system. |
| `RamseySpace.finiteApproximationColouring_for_Milliken` | Generic finite-colour corollary of any topological Ramsey-space basic-neighbourhood theorem. |
| `Milliken.Applications.millikenFiniteColouring k colour` | There exists an infinite strong embedding `B` such that all `r_k(X)` with `X ≤ B` have one colour. |
| `Milliken.Applications.millikenFixedStemFiniteColouring ell k A colour` | Refinement `B ≤ A` with `r_ell(B)=r_ell(A)`, homogeneous for `r_k(X)` of refinements `X ≤ B` which retain that initial stem. |
| `Milliken.Applications.exists_refinement_realising a B h` | A realized finite approximation with carrier inside `B` extends to a refinement `X ≤ B` with `r_k(X)=a`. |
| `Milliken.Applications.milliken1979_homogeneous k colour` | **Direct finite-tree form:** for some infinite strong `B` and colour `c`, every finite height-`k` strong subtree whose carrier is contained in `B` has colour `c`. |
| `Milliken.Applications.truncateApprox h a` | Restriction of a finite height-`k` approximation to height `ell` when `h : ell ≤ k`. Theorems `truncateApprox_approx` and `truncateApprox_trans` establish compatibility. |
| `Milliken.Applications.millikenFixedStem1979_homogeneous ell k h A colour` | **Direct anchored finite-tree form:** a refinement `B ≤ A` retains `r_ell(A)` and all finite height-`k` subtrees in `B` with that stem have one colour. Suitable for a homogeneous-tree `Str_{ell,k}` statement. |

The theorem `millikenFixedStemFiniteColouring` does **not** demand
`ell ≤ k`, since it colours infinite realizers in a basic
neighbourhood. The finite-tree `Str_{ell,k}` theorem does demand
`h : ell ≤ k`, so the prescribed prefix of a finite height-`k`
object is defined.

### Example: colour all finite strong subtrees

```lean
import Milliken.Applications

open Milliken

example (ι : Type) [Finite ι] [Nonempty ι]
    (k : ℕ) (χ : StrongTreeSpace.Approx ι k → Fin 3) :
    ∃ B : StrongEmbedding ι, ∃ c : Fin 3,
      ∀ a : StrongTreeSpace.Approx ι k,
        StrongTreeSpace.approxCarrier a ⊆ StrongEmbedding.range B →
          χ a = c := by
  exact Applications.milliken1979_homogeneous k χ
```

For an anchored `Str_{ell,k}` assertion, call
`Applications.millikenFixedStem1979_homogeneous ell k h A χ`,
with `h : ell ≤ k`. It returns the refined `B`, retained finite
stem and the chosen colour.

## 4. Conditional and proof-level interfaces

Users formalising new Ramsey spaces can reuse the combinatorial lemmas
without introducing an unproved axiom.

| Declaration | Purpose |
| --- | --- |
| `HalpernLauchli.StrongSubtreeHL ι` | Proposition specifying strong-subtree Halpern–Läuchli for every finite dimension and positive number of colours. |
| `HalpernLauchli.HasLevels`, `HasCommonLevels` | Witness a strictly increasing level map for one subtree or for a finite vector of subtrees; `HasCommonLevels.comp` handles coordinatewise composition. |
| `Chapter6.BoundaryHL ι`, `boundaryHL_of_strongSubtreeHL` | Reindex the level-product theorem by the finitely many boundary nodes of a stem (Lemma 6.1). |
| `Chapter6.tupleGraft`, `tupleApprox` | Reconstruct the next selected level from one common-level boundary tuple. |
| `Chapter6.boundaryColor`, `boundaryColor_eq_zero_iff` | Turn a colouring of one-step approximations into the boundary-vector colouring used by A.4. |
| `Chapter6.milliken_of_strongSubtreeHL` | Conditional form: derive the depth-form topological Ramsey theorem from an assumed strong-subtree HL proof. |
| `Chapter6.milliken_onBasicNeighborhoods_of_strongSubtreeHL` | Conditional source-facing basic-neighbourhood form. |
| `StrongTreeSpace.pigeonhole_of_strongSubtreeHL_and_refine` | A.4 from boundary HL and amalgamation refinement. |
| `StrongTreeSpace.approx_comp_stemExtension` | Constructively realize a prescribed finite stem inside a containing strong subtree. |

The unconditional result does not leave Halpern–Läuchli as a theorem
hypothesis: the verified [Hales–Jewett bridge](Milliken/HalpernLauchli/HalesJewettBridge.lean)
provides it.

## 5. Increasing branching and synchronized vector trees

The [merged selected-level development](https://github.com/janhubicka/lean-milliken/pull/3)
has an additional selected-level interface for compressions
`n ↦ L(n)` of a fixed-alphabet tree. The successor set in the
compressed tree is finite, but its degree grows with
`L(n+1)−L(n)`. Its exported geometry includes:

* `HalpernLauchli.SelectedLevelTree.Selection`:
  increasing chosen ambient levels starting at zero;
* `NodeAt S n` and `Child S x`:
  nodes and immediate successors at those selected levels;
* `nodeAtFinite`, `childFinite`, `child_nonempty`:
  local finiteness/nonemptiness;
* `truncate`, `truncate_prefix`, `exists_child_below`:
  ancestry across selected levels;
* `SelectedLevelTree.hdhl_one`:
  the one-dimensional selected-level HDHL case;
* `HalpernLauchli.hdhl_of_all_selected`:
  an **implication** from HDHL on **all** selected-level trees.

This is valuable proof infrastructure, **not yet** an unconditional
arbitrary-tree HL/Milliken theorem: its remaining selected-level
induction must be completed and node-dependent finite branching
requires an additional transport. Do not equate homogeneity of
level-product vectors with homogeneity of **finite vector strong
subtrees**. The latter also requires the synchronized-vector
Milliken extension used by the three-coordinate type-tree application.

## 6. Module map and proof architecture

| Import / file | Responsibility |
| --- | --- |
| `Milliken.Tree`, `Milliken.BranchEmbedding` | Homogeneous strong embeddings and branch/level constructors. |
| `Milliken.AmbientTree`, `Milliken.GeneralTree`, `Milliken.GeneralTree.Published` | Published arbitrary-branching definitions, restrictions and (6.3) finite order. |
| `Milliken.RamseyBasic`, `Milliken.FiniteApprox`, `Milliken.FinitizationOrder` | Approximation system, carriers, book/internal finitisations and A.2. |
| `Milliken.Stem`, `Milliken.StemExtension`, `Milliken.AmalgamationRefine` | Finite-stem realisation and A.3. |
| `Milliken.Chapter6`, `Milliken.PigeonholeLift` | Finite boundary tuples, Halpern–Läuchli reduction and A.4. |
| `Milliken.Closed` | Metric and Tychonoff closedness. |
| `Milliken.HalpernLauchli.HalesJewettBridge` | Hales–Jewett to strong-subtree Halpern–Läuchli. |
| `Milliken.MillikenTheorem` | A.1–A.4 + closedness + Abstract Ellentuck, conditional and unconditional theorems. |
| `Milliken.Applications` | End-user homogeneous finite-colour, original finite-tree and anchored interfaces; published-source tree types. |
| `Milliken` | Full umbrella import, including separate Chapter 3 reconstruction modules. |

## 7. Build, axiom audit, and review

The Lake package pins fixed revisions of Mathlib,
[`lean-ramsey-space-todorcevic`](https://github.com/janhubicka/lean-ramsey-space-todorcevic)
and [`lean-successors`](https://github.com/janhubicka/lean-successors).

```sh
lake update
lake exe cache get
lake build
lake env lean scripts/CheckMilliken.lean
```

GitHub Actions performs `lake build` and checks the transitive
`#print axioms` output for the theorem and application endpoints.
The audit rejects `sorryAx` and any axioms other than the standard
`propext`, `Classical.choice`, and `Quot.sound`. The number of checked
endpoints is maintained alongside the workflow invocation; see
[`scripts/CheckMilliken.lean`](scripts/CheckMilliken.lean) and
[`scripts/check-axiom-log.py`](scripts/check-axiom-log.py).

Review and reference documents:

* [Published-statement crosswalk](docs/PUBLISHED_STATEMENTS.md)
  compares (str1)–(str2), (6.1)–(6.3), Theorem 6.2 and the original
  finite-height formulation, carefully marking remaining theorems.
* [Referee audit dossier](docs/REFEREE_AUDITS.md)
  includes separate source, original-paper and Lean/application
  review briefs and explicit counterexamples.
* [Merged PR #3](https://github.com/janhubicka/lean-milliken/pull/3)
  provides variable selected-level geometry (not the completed induction).
* [Merged PR #4](https://github.com/janhubicka/lean-milliken/pull/4)
  provides the published-source application API and documentation.

### Synchronized vector strong-subtree API

`import Milliken.GeneralTree.Vector` exports `GeneralTree.StrongVectorSubtree U`,
where `U : Fin d → AmbientTree`. Coordinate `i` is an arbitrary locally
finitely branching pruned tree, and all coordinates have **one common**
strictly increasing selected ambient-level sequence:

- `StrongVectorSubtree.coordinate i`, `.levels`, and `.synchronized i`
  provide the coordinate strong trees and their common level map.
- `StrongVectorSubtree.Refines`, `refines_refl`, `refines_trans`, and
  `coordinate_level` give coordinatewise inclusion and synchronization.
- `FiniteVectorApprox U k`, `vectorApprox k S`,
  `FiniteVectorApprox.ext_carriers`, and `vectorApprox_surjective`
  represent finite synchronized vector restrictions (currently with
  infinite-realizer witnesses).
- `vectorApprox_zero_eq` and `VectorBasicNeighborhood a T`
  provide the empty approximation and anchored-neighbourhood interface.
- `HasVectorMillikenFiniteColourProperty U` and
  `HasVectorFixedStemColourProperty U` are **definitions of as-yet-unproved
  properties**, not exported theorems.

For an unconditional **vector Halpern–Läuchli theorem on common-level
node tuples** of homogeneous trees, import `Milliken.Applications.VectorHL`:

```lean
import Milliken.Applications.VectorHL

#check Milliken.Applications.HomogeneousVectorStrongEmbedding
#check Milliken.Applications.homogeneousVectorHalpernLauchli
```

The latter theorem returns a family of independent strong embeddings with
one shared level map; it is proved from the checked Hales–Jewett bridge,
for every finite number of coordinates. **It is not yet a vector Milliken
finite-strong-subtree colouring theorem.** This distinction is essential
when importing into `lean-3-uniform-diaries`.

**A.1 caveat:** the vector type requires positive dimension. Without a
coordinate, no finite approximation can recover the stored level map.

## Finite boundary indexing (A.4 preparation)

`Milliken.GeneralTree.BoundaryIndex S n` packages the ambient successor
boundary of a finite strong stem as an actual finite nonempty type.
`boundaryEquivFin` enumerates this type by `Fin d` with a
stem-dependent dimension: there is **no global branching bound**.
`Milliken.Applications.finiteIndexedStrongSubtreeHL` separately
reindexes the **proved homogeneous-tree** Halpern–Läuchli statement
to any finite coordinate type. These are separate interfaces:
putting them together still requires Halpern–Läuchli on the possibly
different successor cones of a general ambient tree.

## Generic A.1 approximation systems

`Milliken.GeneralTree.generalApproximationSystem U` and
`vectorApproximationSystem U hd` now package all **A.1** laws
(surjective finite restriction, height-zero agreement, separation,
coherence, and reflexive/transitive refinement) into the exact
`RamseySpace.ApproximationSystem` interface for arbitrary pruned
locally finitely branching ambient trees. The basic-neighbourhood
definitions coincide with their published carrier-based counterparts.

**These are A.1 instances only.** A.2 finitisation, A.3 amalgamation,
A.4 pigeonhole, and the final general-tree Ellentuck theorem remain
separate proof obligations. The positive vector dimension is explicit.

## References

* Stevo Todorčević, [*Introduction to Ramsey Spaces*](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf),
  Princeton University Press, 2010, Chapter 6, especially pp. 135–137,
  (str1)–(str2), (6.1)–(6.3), Lemma 6.1, Theorem 6.2,
  Corollaries 6.5–6.6.
* Keith R. Milliken, [*A Ramsey theorem for trees*](https://doi.org/10.1016/0097-3165(79)90101-8),
  *Journal of Combinatorial Theory, Series A* **26** (1979), 215–237.

## General-tree A.4 inverse boundary graft (proved geometry)

The checked `StrongSubtree.boundaryGraftStrong` constructor in
`Milliken.GeneralTree.BoundaryGraftStrong` takes any finite family of
genuine boundary-cone refinements with **one common selected-level
sequence** and returns a genuine infinite strong subtree of an
arbitrary pruned locally finitely branching ambient tree. It preserves
the entire old finite stem, refines its background strong tree, and
has one-step approximation carrier equal to the old finite carrier
united with the range of the tuple of chosen cone roots.

This provides the converse geometric step to the forward tuple encoding
from PR #52. The predecessor and ambient-immediate-successor uniqueness
conditions of the graft are separately proved and compiled, including
the empty stem and the stem/tail cut. Ten dedicated transitive axiom
audit endpoints cover this step.

**Still open:** The arbitrary-node-degree heterogeneous product
Halpern--Läuchli statement `HasGeneralProductHL`/
`HasBoundaryProductHL` introduced in PR #48 is a definition of
the desired standard HL property, not a proved theorem or an axiom.
Its proof and the resulting general A.4/general topological Milliken
theorem remain necessary. The unconditional proof currently covers
homogeneous finite-alphabet trees.

## Canonical A.4 as exactly heterogeneous Halpern--Läuchli (conditional)

`Milliken.GeneralTree.BoundaryTupleRealization` constructs a genuine strong
refinement of an arbitrary locally finitely branching tree from **each**
finite synchronized tuple of actual boundary-cone nodes. The exact finite
one-step carrier is the old stem plus the tuple image. Together with
`StrongSubtree.boundaryTuple` and the inverse graft this gives both directions
of the canonical finite-approximation/HL-tuple correspondence.

`Milliken.GeneralTree.BoundaryTupleHL` proves:
- `boundaryTuple_mem_graftFactors`: every one-step refinement of a
  synchronized boundary graft corresponds to a common-level vector in
  its chosen HL cone factors;
- `canonicalPigeonhole_of_boundaryProductHL`: the canonical
  one-step pigeonhole (Lemma 6.1) follows *exactly* from the
  heterogeneous cone-product HL property;
- `generalPigeonhole_of_generalProductHL`: the published full A.4
  follows by finite-boundary reindexing plus checked A.3;
- `abstractRamseySpace_of_generalProductHL`: full abstract
  A.1--A.4 data under the **sole standard general product HL premise**.

These are conditional formal implications. They do **not** declare HL
as a new Lean axiom or prove the unrestricted `HasGeneralProductHL`
statement. To finish Todorčević's unrestricted Theorem 6.2, that
heterogeneous HL theorem and the appropriate general-tree closedness
must still be proved. The library's homogeneous main theorem remains
unconditional.


## General-tree approximation-code geometry (closedness preparation)

The code-frontier development recovers selected ambient ranks and the full
node carrier from maximal levels of a full sequence of realised finite
approximations. Under finite-prefix realizability the ranks strictly
increase and each carrier node belongs to the unique matching source
frontier. This is a step toward unrestricted Tychonoff closedness; the
point-of-code strong-subtree construction remains to be completed.


## General-tree closedness and the exact conditional topological theorem

`Milliken.GeneralTree.generalIsMetricallyClosed` and
`generalIsTychonoffClosed` establish the textbook closedness of the
entire strong-tree approximation space for every arbitrary pruned locally
finitely branching rooted tree. No uniform branching degree is used.

`generalMilliken_of_generalProductHL U hHL` derives the textbook
Abstract Ellentuck/Milliken topological Ramsey conclusion from the
**single explicit heterogeneous product Halpern--Läuchli premise**.
That general HL theorem remains to be proved unconditionally. The
conditional result is not an unconditional general-tree theorem.


## General heterogeneous Halpern–Läuchli induction (in development)

The source-faithful Todorčević Chapter 3 induction over a homogeneous
alphabet enumerates its finite successor list and therefore handles
arbitrarily **large finite branching degrees across different input
alphabets**. It does not, however, prove a single theorem for one
ambient tree whose branching degree varies with the node and is
unbounded across its levels: the checked `HDHL ι d` and
`StrongSubtreeHL ι` still use the fixed `Node ι = List ι` type.

`GeneralTree.HeterogeneousDensity` now starts the port of the same
induction to the actual ambient `StrongSubtree U` coordinates.
It verifies finite/nonempty common selected-level products, defines
heterogeneous coordinate matrices, and checks elementary density
calculus without a global degree bound. `HasHeterogeneousHDHL`
remains explicitly an **unproved property**. Its multi-coordinate
induction, subsequent strong-tree product HL, and the unconditional
heterogeneous Milliken theorem are not yet certified.


### Verified heterogeneous HDHL base case

`GeneralTree.heterogeneousHDHL_one` proves Todorčević's
one-dimensional highly-dense-set statement for a **genuine arbitrary
locally finitely branching tree**, rather than merely for a fixed
homogeneous `List ι` tree. It projects a highly dense unary set to a
one-coordinate matrix, preserving both density and containment.
The higher-dimensional heterogeneous induction and resulting
`HasBoundaryProductHL` are still required for general Milliken.


### Heterogeneous cone-density calculus

`HeterogeneousMatrix.DenseAbove` and `restrictAbove` use
the actual descendant cones of arbitrary strong coordinate trees;
`fillOutsideAbove` completes a locally dense cone matrix to a
globally dense one by filling the other n-th source-level nodes.
The relevant density and carrier transport identities, and downward
closure of product density, are checked as prerequisites of the
unbounded-branching Chapter 3 asymmetric dichotomy.
