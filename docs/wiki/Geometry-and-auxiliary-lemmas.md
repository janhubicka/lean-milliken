# Geometry and auxiliary lemmas: a human-readable map

This is an inventory of the auxiliary mathematics in the Lean proof that is either compressed into a sentence in the book, or needed for the representation choices of the formalisation. It aims to answer a researcher’s question: **what reusable results are available beyond the final theorem?**

**Scope:** `GeneralTree` over arbitrary rooted pruned locally finite trees, no uniform degree bound. The historic fixed-alphabet code was an independent route, not part of the proof dependency of `generalMilliken_unconditional`.

## 1. Ambient tree geometry

The base `Milliken.AmbientTree` is a Mathlib rooted tree with `finite_children` and `has_child` fields. Hence every individual frontier is finite and can be processed by finite induction; children need not be globally bounded in cardinality.

| Lemma / module | Human meaning | Reusable purpose |
| --- | --- | --- |
| `AmbientTree.level_covBy` | Moving along an immediate ambient edge raises height by exactly one | Relate child cones to skipped selected heights |
| `AmbientTree.level_lt` | Strict ancestors have strictly smaller heights | Forbid two comparable distinct nodes at one selected level |
| `AmbientTree.eq_of_le_of_level_eq` | Comparable nodes at the same ambient level are equal | Unique representatives and exact frontier identities |
| `StrongSubtree.sourceLevel_nonempty` | Every source level has a node | Choose witness for each selected level and prove finiteness of lower approximations |
| `StrongSubtree.initialPart_zero`, `initialPart_mono` | The empty initial approximation is literally empty; truncation is monotone | A.1, handling `n=0` uniformly |
| `GeneralTree/Ancestry.lean`, `SourceLevels.lean`, `BoundaryAncestor.lean` | Descendants and unique selected ancestors exist at prescribed earlier source levels | No-ghost condition, refinement, source-level selection |
| `GeneralTree/FiniteLevels.lean`, `MaxLevel.lean` | Every fixed level and finite stem really is finite; its maximal nodes are its last selected source level | A.2(1), boundary-index finiteness, approximation enumerations |

The data `StrongSubtree.predecessor_exists` is not redundant with its forward ambient-successor uniqueness clause. The binary-tree ghost example is recorded in `docs/REFEREE_AUDITS.md`. A safe refactor may **reformulate** this condition, but should not drop its mathematical content without proving a replacement.

## 2. What the book calls finitisation and amalgamation

- `bookLeFin_lowerFinite` shows each finite approximation has only finitely many predecessors in the **exact** book order: a finite carrier bounds source height, and a finite ambient set contains only finitely many possible fixed-height approximation carriers.
- `refines_iff_forall_bookLeFin_r` shows infinite strong-subtree inclusion is detected by a suitable finite witness in the book order for every `r_n). This is A.2(2), not a postulate.
- `bookLeFin_prefix_compatible` aligns two finite prefixes and finds a suitable still-shorter finite approximation. The maximal-level clause is essential here; carrier inclusion alone gives an easier but *different* relation.
- `generalAmalgamation_nonempty` and `generalAmalgamation_refine` prove both halves of A.3: a compatible stem can be realised in a refinement, and the chosen depth of `B` can be protected while forcing all extensions of the stem into a designated subtree.
- `StrongSubtree.thinStrong` and `protectedIndex` (modules `Thinning*`, `Protected*`) synchronize chosen future source levels **without changing a fixed initial stem**.
- `StrongSubtree.mixedStrong` and source/frontier-sector lemmas (modules `Mixed*`) allow different genuine tails in **used** and **unused** frontier sectors. Merely taking union of arbitrary subtrees would not ensure a strong subtree.

The proof of general A.3(2) uses both a protected thinning and mixed graft, which is substantially more elaborate than the published “easily seen” explanation.

## 3. Boundary-cone coding of one-step extensions

For a strong tree `T` and a source cut `n`, define the actual **source boundary** to be the finite set of immediate ambient child cones above the last kept frontier. For `n=0` there is a single distinguished root cone.

The files `BoundaryIndex`, `BoundaryCones`, `BoundaryTuple`, `BoundaryTupleRealization`, `BoundaryBijection`, `BoundaryGraftData`, `BoundaryGraftPredecessor`, `BoundaryGraftSuccessor`, and `BoundaryGraftStrong` collectively establish:

1. Every one-step extension of `r_n(T)` is coded by a tuple of boundary-cone nodes at one synchronized new ambient level.
2. Such a tuple defines exactly the extension carrier `r_n(T) ∪ `the tuple's nodes`; no extra points are introduced.
3. If every boundary cone is replaced by a genuine strong subtree, with one selected-level map, there exists a genuine strong graft.
4. The graft's `r_n` is **exactly** the original `r_n(T)`; the graft is a strong refinement of `T`.
5. The new source-level-`n` frontier is **exactly** the set of selected coordinate roots.
6. All of this includes `n=0` and strong subtrees whose root lies below the ambient root.

The modules therefore formalise book equations (6.4)–(6.8), not only the pigeonhole colour conclusion.

## 4. Highly dense products, bad sections and stabilization

The heterogeneous version of Chapter 3 is supported by a substantial calculus, rather than a theorem postulate.

| Files / declaration | Readable meaning |
| --- | --- |
| `HeterogeneousDensity`: `HeterogeneousMatrix`, `DenseAt`, `OnLevel`, `HeterogeneousHighlyDense` | Matrix of coordinate node sets, density at a source index, common support level, and the robust density-of-`Q` antecedent |
| `HeterogeneousHDHLBase`: `heterogeneousHDHL_one` | A one-dimensional highly dense set already contains the desired dense coordinate set |
| `HeterogeneousRemark38`: `heterogeneousRemark38Levels` and complement exclusion | Pick source scales so a complementary obstruction cannot be dense between any designated pair of scales |
| `HeterogeneousLemma315Proof` | Convert an attempted failure of positive density to an actual complementary somewhere-dense matrix; tail normalization protects earlier sections |
| `HeterogeneousLemma316Proof` | Obtain a suitable last-coordinate witness with a front-coordinate matrix dense on a common higher support level |
| `HeterogeneousFinalInduction`: `HeterogeneousSectionFusionState`, `HeterogeneousSectionFusionStep` | Process actual finitely many children one by one, maintaining prior positive section witnesses and density |
| `HeterogeneousCumulativeStabilization` and `HeterogeneousProtectedFusionLimit` | Form a fusion limit with common selected levels and protected original root/frontier coverage |
| `heterogeneousReducedHDHL_of_previous` | Synchronised reduced `(d+1)`-dimensional density theorem assuming only HDHL for *all* `d`-dimensional front families of the same ambient |
| `HeterogeneousBinaryStrongHL`, `HeterogeneousFiniteStrongHL` | Convert highly dense HL into synchronized monochromatic infinite level products for arbitrary finite colours |

These results distinguish **global density at a source index** from density *above a specific base tuple*, and separate ordinary from **restricted** somewhere-density. Mixing these notions would falsely close the induction.

## 5. Compression and common-ambient transport

The source-index selection `f` can have arbitrary gaps. To avoid erasing nodes, `CompressedSource*` modules preserve *every* original source node at every selected index `f(n)` and re-index its ambient height as `n`. This requires a genuine new `AmbientTree` with its own:

- order, root and unique finite ancestor chain;
- predecessor operation and exact new height;
- meet/greatest common ancestor;
- finite, nonempty child sets.

The **heterogeneous wedge** `WedgeNode.ambientTree` combines these per-coordinate compressed trees by adding one fresh root, then `HeterogeneousWedgeComponentCones` proves that each component is a genuine strong subtree of this new ambient, with the same `n+1` levels for all coordinates.

Crucial bridge lemmas:

- `CompressedSourceSelection.compressedAmbient_level_eq_index`: the compressed height is exactly the source index.
- `WedgeNode.ambient_level_embed`: tagged component nodes have height one plus their compressed height.
- `WedgeNode.componentStrong` and `componentStrong_levels`: no missing successors and exact synchronization.
- `HeterogeneousCompressionWedge.decodeMatrix_original_denseAt` and `decodeMatrix_original_subset`: a positive matrix in the wedge yields a dense original matrix in the target colour.
- `heterogeneousSomewhereDense_to_restricted_id`: move different coordinate bases to one common penultimate source level.
- `HeterogeneousCompressionWedge.no_wedge_complement_somewhereDense`: an obstruction in the wedge would give a forbidden restricted obstruction in the original product.

The last two results are not optional boilerplate. They are the logical justification for invoking the reduced induction. The type of the recursive ambient changes, which forces `universalHeterogeneousHDHL` to quantify over **every** ambient tree before induction.

## 6. Ramsey-space closedness and colours

- `GeneralTree/CodePoint.lean`: reconstruct a single infinite strong tree from a coherent system of finite approximation codes.
- `GeneralTree/GeneralClosed.lean`: establish `generalIsMetricallyClosed` and `generalIsTychonoffClosed`. The image is closed in the actual product of discrete finite approximations, not merely closed for a restricted family of witnesses.
- `GeneralTree/CanonicalPigeonhole.lean`: use protected A.3 to lift the canonical stem pigeonhole theorem to all published depths.
- `GeneralTree/UnconditionalHLAPI.lean`: unconditional product HL, boundary HL, general pigeonhole and abstract Ramsey-space witnesses.
- `GeneralTree/HeterogeneousUniversalMilliken.lean`: unconditional topological theorem.
- `Milliken/FiniteColourRamseySpace.lean`: finite-colour consequence of the *generic* topological Ramsey property (independent of any particular strong tree).
- `GeneralTree/Original1979Conditional.lean`: extend already realised finite prefixes into refinements of a given infinite tree, then obtain the realised finite-colour theorem.
- `GeneralTree/FixedStemUnconditional.lean`: preserve an arbitrary initial `ell` source levels and homogenise every further infinite refinement with that stem.

## 7. Compact examples of subtle failures

**Ghost source levels.** Forward unique extension at selected heights does not forbid unconnected extra later-level nodes. `predecessor_exists` handles this.

**Wrong rank.** An original ambient height of `(P i).levels (f n)` is not compressed height `n`; confusing them breaks the wedge level proof.

**Wrong ambient in the induction hypothesis.** The common-root wedge is not the original ambient; a hypothesis quantified only over `U` cannot be applied to it.

**Incomplete compression.** Choosing one node from each selected source level destroys full-product density; all selected-level nodes must survive.

**Positive-only transport.** Mapping positive matrices back does not rule out negative density in the newly built wedge; the no-complement lemma is necessary.

**Conditional theorem misread as proved HL.** A lemma named `..._of_boundaryProductHL` proves an implication from a hypothesis `HasBoundaryProductHL U`; the premise is discharged by a separately proved `boundaryProductHL_unconditional` endpoint.

**1979 theorem inferred from realised approximations alone.** `exists_refinement_realising_general` is *relative extension*: its input already includes an infinite realiser. The intrinsic finite-tree extension and type equivalence are still required for literal `S_k(U)` coverage.

**Scalar versus vector Milliken.** Product HL makes node **tuples** monochromatic. Vector Milliken colours whole finite synchronized **subtree vectors**. The latter is still a stated property, not an exported unconditional theorem.

## 8. Audit and maintenance principles

Keep the main proof path minimal and let CI guard its kernel arguments. Any module slated for deletion must be unreachable from all supported public theorem endpoints and genuinely optional mathematical interfaces. Downstream application libraries should pin and independently compile their declared dependencies. Before modifying `StrongSubtree` or `FiniteApprox`, add statement-level regression tests in Lean. For further historical background, compare the explicit [proof architecture](Proof-architecture.md) with [published statements](Published-statements.md).
