# How the checked proof works, and why it differs from the book

This page is a mathematical explanation, **not** a Lean tactic trace. The statements and file locations were checked against `janhubicka/lean-milliken` at `8bb11529b1631288954248eee6da53416d5b073e`. Source: Todorčević, *Introduction to Ramsey Spaces* (2010), Chapters 3, 5, 6; Milliken (1979), published abstract.

## The mathematical goal

Start with a rooted tree `U` that has *finitely many* immediate successors at each node and *at least one* successor everywhere. No single number must bound the degree of every node. Strong subtrees may begin above the ambient root. There is a strictly increasing sequence of ambient heights

```text
  L(0) < L(1) < L(2) < ...
```

at which we retain the strong tree's source levels. If `x` is at source level `j`, **every** immediate child `y` of `x` in `U` has exactly one selected descendant at source level `j+1` above `y`. Every non-root selected node must have a predecessor on the preceding selected level.

The space `S∞(U)` of infinite strong subtrees is refined by carrier inclusion. Its `n`th approximation `r_n(T)` is the union of the first `n` selected levels, not the set of all ambient nodes below ambient height `n`. The book theorem says: every set with the Baire property in the Ellentuck topology of these basic neighbourhoods is Ramsey, and every meagre set is Ramsey null.

## Read the proof from right to left

```text
Heterogeneous highly-dense Halpern–Läuchli (all dimensions, all U)
       ↓ finite colours + synchronized source-index selection
Product strong-subtree Halpern–Läuchli for locally finite boundary cones
       ↓ encode each one-step stem extension as a boundary tuple
Canonical one-step pigeonhole / Lemma 6.1
       ↓ published A.3 protection of arbitrary finite stem at depth d
A.4 for the literal book finitisation (6.3)
       + A.1, A.2, A.3, Tychonoff closedness
       ↓ checked Abstract Ellentuck theorem
General-tree topological Milliken / Theorem 6.2
       ↓ finite colouring of realised approximations, finite-stem extension
Milliken 1979-style finite-colour conclusion (realised finite objects)
```

No part of this argument assumes a homogeneous alphabet. The general theorem depends on the external **checked Abstract Ellentuck library**, not on the historical `StrongEmbedding` homogeneous proof.

### 1. The published strong-tree space and its geometric axioms

The ambient is `Milliken.AmbientTree` with a Mathlib `RootedTree`, finite child sets, and no terminal nodes. `GeneralTree.StrongSubtree` records the carrier, root, selected levels, ancestor compatibility and two complementary local coverage laws.

There is a real issue when encoding (str1)–(str2) merely as equations of carriers: the forward unique-extension law does **not** prevent extra later-level nodes disconnected from the chosen preceding frontier. For example, in the binary tree with levels `0,2,3,...`, choose `00` and `10` on level 2 and include `010` on level 3 in addition to all mandated successors. The extra node has no selected level-2 ancestor. The Lean structure therefore explicitly requires `predecessor_exists`, encoding *regular rooted strong tree* rather than only a one-way extension scheme.

The proof also has to keep two ranks separate. `U.level x` is the number of ambient predecessor steps from the root. `S.levels j` is the ambient height of source level `j`. `r_n S` cuts at **source** height `n`, regardless of the sizes of ambient gaps. Many non-obvious transport lemmas exist solely to stop these two ranks being accidentally confused.

A.1 comes from `GeneralTree/ApproximationSystem.lean` and `Coherence.lean`. A.2 uses the **book's exact** order

```text
    a ≤fin b  iff  (a = b = ∅)
                      or
                  (carrier(a) ⊆ carrier(b)
                   and maximalLevel(a) ⊆ maximalLevel(b)).
```

The substantive checks are `bookLeFin_lowerFinite` (`LowerFinite`), `refines_iff_forall_bookLeFin_r` (`OrderRealization`), and `bookLeFin_prefix_compatible` (`PrefixFinitization`). The A.3 refinement argument (`PublishedAmalgamation`) aligns the cut level, thins the larger tree without losing its protected prefix, and glues an `X`-tail inside the used frontier sectors while retaining the original tree in unused sectors. This is much longer in Lean than the book's sentence “A.1, A.2 and A.3 are easily seen”.

### 2. Halpern–Läuchli: a proof for variable local degree

The book's proof of Lemma 6.1 invokes its product strong-tree Halpern–Läuchli Theorem 3.2. Earlier versions of this formalisation used lists of letters from one fixed alphabet. They do not by themselves cover `U` with degree changing from node to node, possibly unbounded.

The unrestricted implementation instead defines `HeterogeneousMatrix P` for a finite `Fin d` family `P : Fin d → StrongSubtree U`. Each matrix is a Cartesian product of arbitrary coordinate subsets, with a containment proof. It is **dense at source index `k`** if every node on source level `k` of every coordinate has a descendant in that coordinate set. The `HeterogeneousHighlyDense P Q` predicate strengthens an ordinary level-by-level nonemptiness assertion: for every target source index `k`, it supplies a deeper scale at which *every sufficiently dense matrix* contains a `Q`-point above each level-`k` product tuple.

The all-dimensional HDHL theorem `universalHeterogeneousHDHL` is proved by **induction simultaneously over every ambient tree**. This universal quantification is essential and is not merely an aesthetic strengthening: the induction step constructs an entirely **new** ambient.

At dimension one, project a highly dense set onto its sole coordinate (`HeterogeneousHDHLBase`). At dimension `d+1`, Todorčević's Remark 3.8 gives a strictly increasing selection `f` of **source indices** on which no restricted somewhere-dense matrix can occur inside the complement of the positive colour. A reduced induction for a synchronized family then turns absence of complementary density into a positive matrix dense at one source step.

The hard part is connecting an arbitrary input family, whose coordinates may have different roots and level sequences, to that *synchronized* reduced induction.

### 3. Full source-level compression and the new common-root wedge

For each factor `P_i`, construct a new locally finite tree `C_i` whose nodes are *all* original source nodes on source levels `f(0), f(1),...`, tagged with their compressed source index. Its new ambient height of a tagged node `(n,x)` is exactly `n`; it is **not** the old ambient height `(P_i).levels(f n)`.

**Crucial difference from a naïve proof:** `C_i` generally cannot be treated as a strong subtree of the original tree. Collapsing long gaps changes the number of immediate children. The construction retains **all** selected nodes, not just one representative per cone; thinning would break density transfer and the somewhere-dense obstruction.

The factors `C_i` have different underlying types, so cannot be directly passed as coordinates of the existing reduced theorem `Fin d → StrongSubtree V` for a *single* ambient type `V`.

Make a disjoint forest and adjoin one fresh common root `★`:

```text
                         ★                      depth 0
                /        |        \
          (0,root)   (1,root)   ... (d−1,root)   depth 1
            / \        / \                    depth 2
          .......    .......
```

Every tagged coordinate `(i,t)` has depth `1+depth_{C_i}(t)`. Nodes with different tags meet at `★`; within one component, order/parent/meet are those of `C_i`. The new root has `d` children; elsewhere degrees are the finite degrees from the corresponding compressed trees. For positive `d`, this is again a pruned locally finite `AmbientTree`.

Each component yields a **genuine** `StrongSubtree V`, with one common level map `n ↦ n+1`. This is not just a propositional assertion of common levels: `HeterogeneousWedgeAmbient`, `HeterogeneousWedgePred`, `HeterogeneousWedgeHeights`, `HeterogeneousWedgeComponentCones` and the compressed-source modules construct all predecessor/order/height witnesses.

Now the induction hypothesis for **every ambient** can be applied to `V`, despite its having been freshly constructed.

### 4. Why both colours and *failure* of density must transport

Merely encoding positive matrices in the wedge is not enough. The reduced dimension induction has the hypothesis “there is no ordinary somewhere-dense product matrix contained in the complementary colour”. Remark 3.8 initially excludes *restricted* somewhere-dense matrices only between specially selected source indices in the original product.

The proof uses a **contrapositive** transport:

1. Suppose the wedge complement admits an ordinary somewhere-dense matrix. Its coordinate bases may lie at different source indices.
2. Move those bases down the cones to a common penultimate source index, preserving density. The case `d>0` ensures the relevant index is meaningful.
3. Decode the matrix to the **full** compressed source trees, preserving its level support, ancestor relation, and Cartesian product.
4. Transfer this compressed obstruction to a restricted original-tree obstruction between indices `f(p)` and `f(q)`, contradicting Remark 3.8.

The main checked statements for these steps are `heterogeneousSomewhereDense_to_restricted_id` (`HeterogeneousIdentityBridge`), `decodeMatrix_somewhereDense` and `no_wedge_complement_somewhereDense` (`HeterogeneousWedgeComplementTransfer`), plus `decodeMatrix_original_denseAt` and `decodeMatrix_original_subset` (`HeterogeneousWedgeCompressionTransport`).

After ruling out the wedge obstruction, invoke `heterogeneousReducedHDHL_of_previous` (`HeterogeneousReducedInduction`). Decode the positive one-dense wedge matrix back into an original one-dense matrix contained in `Q`. This proves `heterogeneousRestrictedReduced_of_previous_universal`, closes the universal `d+1` induction, and discharges the heterogeneous HL hypothesis **without any new axiom**.

### 5. The reduced induction itself, unpacked

The proof under a synchronized input (`HeterogeneousReducedInduction`) is far from a one-line recursive call:

- `HeterogeneousLemma315Proof` builds a negative somewhere-dense obstruction when the expected positive sections persistently fail.
- `HeterogeneousLemma316Proof` obtains positive last-coordinate sections with front-coordinate matrices satisfying both a density requirement and a common upper source-level support bound.
- `HeterogeneousFinalInduction` processes the **actual finite successor set** of the last coordinate root. It accumulates section witnesses without losing earlier positive sections.
- `HeterogeneousCumulativeStabilization` and `HeterogeneousProtectedFusionLimit` construct a limit family, retaining the original roots and enough next-frontier coverage to convert density in the refinement back to density in the original input.

The book suppresses much of this engineering because it is mathematically standard once the fusion and cone arguments are understood; the Lean version has to make preservation of protected stems, local finiteness, and synchronized levels explicit. A detailed introduction to these helper structures is in [Geometry and auxiliary lemmas](Geometry-and-auxiliary-lemmas.md).

### 6. Back to Lemma 6.1 and the Abstract Ellentuck theorem

Fix `[n,T]` and a colouring of finite height-`n+1` strong trees. Enumerate the *finite set* of actual ambient children above the level-`n−1` boundary (for `n=0`, the single root cone). A tuple of compatible nodes from these cones encodes a one-step extension of the finite stem. This is the book's equations (6.4)–(6.7).

Use synchronized product HL on these actual cones, then graft all selected cone trees onto the preserved first `n` source levels of `T`. The resulting `S ∈ [n,T]` has its entire next-level approximation family inside one of the two colours. This is the book's (6.8), a **genuine strong subtree**, not merely a carrier set.

The implementation separates this into `BoundaryTupleHL`, `BoundaryGraftStrong`, and `CanonicalPigeonhole`. The last step uses the *already proved A.3* to upgrade canonical stems to the full A.4 clause with arbitrary depth and a protected prefix.

Together with metrically/Tychonoff closedness (`GeneralClosed`), the separately formalised **Abstract Ellentuck theorem** from `lean-ramsey-space-todorcevic` gives `IsTopologicalRamseySpaceTextbook`. That target quantifies over *all* sets with the Baire property and *all* meagre sets, not only clopen colour classes. This is `generalMilliken_unconditional`.

Finite colour classes on the approximation space are Ellentuck open. The generic theorem in `Milliken/FiniteColourRamseySpace.lean` converts this to a colouring of all realised finite approximations. The theorem `exists_refinement_realising_general` shows that a realised finite prefix contained in `B` can be made the prefix of an infinite refinement of `B`. This gives `milliken1979_general_unconditional` and its protected-stem variants.

**Important remaining identification:** a finite tree not *given* with an infinite realiser has not yet been directly represented by `FiniteApprox`. For the literal 1979 assertion and Corollary 6.5 an **intrinsic finite strong tree extends to an infinite one** lemma and corresponding bijective interface should be proved.

## Differences from the printed proofs: summary

| Printed proof | Formal proof: explicit strengthening/change | Why necessary |
| --- | --- | --- |
| “A.1, A.2, A.3 easily seen” | Separate finite level/cardinality, order-realisation, prefix compatibility, protected thinning and mixed graft | Avoid assuming relative extension or order equivalences |
| `S_k(U)` intrinsically finite | `FiniteApprox U k` stores an infinite realisation | Convenient for A.1/closedness but creates a separate source-identity obligation |
| “Strong subtree” regularity implicit | `predecessor_exists` explicitly rules out ghost levels | A one-way successor existence condition is insufficient |
| Product HL invoked | All-dimensional highly dense heterogeneous HL separately proved | General local finite degrees need not be bounded by one alphabet |
| Level changing suppressed | Full selected-source-level compression preserves *every* source node | Dense matrices cannot survive arbitrary thinning |
| Distinct coordinate trees as products | Common-root wedge with synchronized true strong subtrees | Recursive theorem requires coordinates in one ambient type |
| Complementary matrix excluded | Explicit **negative** density transport and common-base alignment | Prevents an unjustified application of the reduced dichotomy |
| Dimension induction | Universal over *every* ambient, not fixed `U` | Needed because the wedge ambient differs from original |
| One-step boundary argument | Explicit boundary bijection + graft with root/n=0 cases | Lean verifies the actual object is a strong subtree |
| Abstract Ellentuck invoked | Imported checked A.1–A.4 plus closedness-to-Baire-property implementation | Ensures the theorem is topological, not just finite-colour |
| Original 1979 paper's finite trees | Quantified over realised finite approximations | Not yet proof of all intrinsic finite strong subtrees; separate task |

## Reading order for contributors

1. `Milliken/AmbientTree.lean`, `Milliken/GeneralTree.lean`, `GeneralTree/Published.lean`.
2. `GeneralTree/ApproximationSystem.lean`, `PrefixFinitization.lean`, `PublishedAmalgamation.lean`, `GeneralClosed.lean`.
3. `GeneralTree/HeterogeneousDensity.lean`, `HeterogeneousHDHLBase.lean`, `HeterogeneousRemark38.lean`.
4. `GeneralTree/HeterogeneousLemma315Proof.lean`, `HeterogeneousLemma316Proof.lean`, `HeterogeneousReducedInduction.lean`.
5. Compressed source and wedge modules, `HeterogeneousWedgeComplementTransfer.lean`.
6. `HeterogeneousUniversalMilliken.lean` (final proof), `UnconditionalHLAPI.lean` (public endpoints).
7. `BoundaryGraftStrong.lean`, `BoundaryTupleHL.lean`, `CanonicalPigeonhole.lean`, `FixedStemUnconditional.lean`.

An import of `Milliken.GeneralTree.UnconditionalHLAPI` is usually sufficient for the main unrestricted HL/Milliken endpoints; `Milliken.GeneralTree.FixedStemUnconditional` adds protected finite-approximation colours. For the diary project, prefer these rather than the historical homogeneous `Milliken.Applications` or `Milliken.MillikenTheorem`.

## What this document does *not* certify

It does not constitute a full mechanical proof of *the full 1979 article's internal proof presentation*. The paper's published abstract was checked; its full text is still needed for a proof-by-proof comparison. Nor do verified scalar HL and Milliken imply a finite **vector** Milliken theorem without another argument. See the [statement crosswalk](Published-statements.md) and [audit tracker](../audits/AUDIT_TRACKER_2026.md).
