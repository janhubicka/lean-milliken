# The intrinsic finite-tree extension lemma (work in progress)

**Status:** The first genuinely intrinsic finite-subtree representation has been introduced in [Milliken PR #146](https://github.com/janhubicka/lean-milliken/pull/146). The forward map from a realised approximation is implemented; the reverse extension is not yet checked. This page gives the complete intended **English proof**, its precise hypotheses, and failure tests. It must not be labelled an accomplished Lean theorem until the final equivalence and coloured corollary compile.

## Why this is a distinct lemma

Todorčević §6.1 defines `S_k(U)` as **all** strong subtrees of height `k`. Formula (6.2) implicitly identifies them with the `k`th truncations of infinite strong subtrees of `U`. Milliken's 1979 abstract similarly colours all finite strongly embedded subtrees. Our original `FiniteApprox U k` instead stores

```lean
carrier : Set U
realised : ∃ S : StrongSubtree U, carrier = S.initialPart k
```

Thus `exists_refinement_realising_general` is a **relative extension** theorem for an already realised carrier, rather than a proof that every intrinsic finite strong subtree has an infinite extension.

The new `IntrinsicFiniteWitness U k` contains no infinite realiser. It records a finite carrier, exactly `k` strictly increasing selected ambient heights `levels : Fin k → Nat`, a selected root, and the two genuine finite strongness requirements (no ghost nodes and exactly one selected representative per immediate ambient-child cone at each *internal* step). For `k=0` the carrier is empty. `IntrinsicFiniteApprox U k` forgets which witness proves the carrier is intrinsic, so colourings are of finite *sets of nodes*, as in the book.

## Finite-to-infinite extension: explicit proof

Let `F` be an intrinsically strong finite subtree of height `k>0`, with root `r` and ambient selected levels

```text
      L(0) < L(1) < ... < L(k−1).
```

Write `E` for its last selected frontier `{x ∈ F : level_U(x)=L(k−1)}`. We have `E ≠ ∅` by induction: the first source level is `{r}`, and each selected node has an ambient child, which has a unique selected representative at the next prescribed level.

Define a new infinite level sequence `L∞` by

```text
       L∞(j) = L(j),                   j < k,
       L∞(j) = L(k−1) + (j−k+1),      j ≥ k.
```

It is strictly increasing: all internal comparisons follow from the finite strongness witness; the boundary comparison is `L(k−1) < L(k−1)+1`; the remaining comparisons increase by one.

Let `Tail(E) = {z ∈ U : ∃ e ∈ E, e ≤ z}` be the union of the **complete ambient descendant cones** rooted at the final frontier. Define the infinite carrier

```text
        S = F ∪ Tail(E).
```

The last finite frontier is included in both terms. This double description does not create extra nodes.

**Selected levels:** Every node of `F` has ambient height among `L(0),...,L(k−1)`. Every node of `Tail(E)` is at ambient height at least `L(k−1)`, and every such height appears among the linear tail `L∞(k−1+t)=L(k−1)+t`. Thus the full carrier lies on the prescribed selected levels.

**Root and predecessor:** `r` is retained and lies below all nodes of `F` and below their descendants. At source levels `1,...,k−1`, a selected predecessor exists by the intrinsic hypothesis. Later, `Order.pred z` is on the preceding ambient level and remains in the *same complete final-frontier cone*. Consequently it belongs to `S`.

**Unique ambient-successor representatives (early source steps):** If `j<k−1` and `x∈S` lies on source level `j`, its ambient height is strictly below that of every node of `E`, so `x∈F`. By intrinsic strongness, each immediate ambient-child cone of `x` contains exactly one member of `F` at `L(j+1)`. No new `Tail(E)` member can lie at an earlier height. At the last finite height `L(k−1)` any tail member has the height of a final frontier node below it, so equality of comparable ambient nodes at the same height forces it to be that frontier node. Thus uniqueness is unchanged.

**Unique ambient-successor representatives (after the final frontier):** At source index `j≥k−1`, every source-level-`j` node lies in some complete cone `Tail(E)`. If `x⋖y` is any immediate ambient child, then `y∈Tail(E)` and has ambient height exactly `L∞(j)+1=L∞(j+1)`. It is the required *unique* representative: any further selected `z` above `y` at the same ambient height equals `y`.

It follows that `S : StrongSubtree U` is a genuine infinite strong tree, and **its first `k` source levels are exactly `F`**. The reverse implication is the already compiled `intrinsicWitnessOfStrong` constructor.

For `k=0`, `F=∅`; simply take `identityStrongSubtree U`, whose `r 0` is empty.

### Alternative Lean implementation

Instead of proving all clauses for `S=F∪Tail(E)` directly, reuse
`StrongSubtree.LevelChoice.toStrongSubtree` from `GeneralTree/ChosenStrong.lean`.

1. Extend the `Fin k` level sequence as above.
2. Start from the identity ambient strong tree and choose root `r`.
3. At internal stages `j<k−1`, whenever a currently selected node `x` belongs to `F`, select the **unique finite** representative of each child cone at `L(j+1)`.
4. For all other inputs (including all stages after the final finite level) use `longConeRepresentative` from `GeneralTree/LongCones.lean`.
5. Prove by induction on `j<k` that `LevelChoice.level j` is **exactly** `F∩U.levelSet(L(j))`. Forward inclusion uses finite unique-successor choice. Reverse inclusion uses finite predecessor-existence and `immediateChildren_eq_of_common_descendant`.
6. The reusable constructor then supplies all infinite strong-tree laws, and equality of first `k` source levels establishes the desired witness.

The first route has a simpler *mathematical statement*, the second route reuses more already verified Lean geometry. Both avoid assuming what is to be proved.

## From extension to the literal finite-colouring theorem

Once `IntrinsicFiniteApprox.toRealised` is proved:

1. `FiniteApprox.toIntrinsic` and `IntrinsicFiniteApprox.toRealised` preserve carriers in both directions.
2. Since both finite object types identify elements by **carrier**, their composites are identities. We obtain a genuine type equivalence for every `k` (including `k=0`).
3. A colouring `χ : IntrinsicFiniteApprox U k → Fin colours` can be precomposed with `FiniteApprox.toIntrinsic`, and the already proved `milliken1979_general_unconditional` applied.
4. If `F` is intrinsic and its carrier lies inside the resulting infinite `S`, convert it to a realised approximation, then use the proven colour constancy and convert back on carriers. This yields the literal quantification over all finite strong subtrees as in 1979 and Todorčević Corollary 6.5.
5. A strengthened relative extension statement can be obtained by composing absolute extension with the existing `exists_refinement_realising_general`, when the finite intrinsic carrier is contained in a specified infinite strong tree.

## Adversarial tests

- **k=0:** the only intrinsic carrier is empty. The arbitrary recorded witness root and empty levels must not affect object equality.
- **k=1:** an arbitrary ambient node `r` is a valid one-level finite strong tree; there are no internal successor constraints, but all its complete descendant cones must be added after extension.
- **Large level gap:** if `L(0)=0`, `L(1)=17`, every immediate ambient-child cone must contain exactly one selected level-17 representative; the completion must not insert forbidden intermediate nodes before level 17.
- **Node-dependent unbounded degree:** at each finite level each node has finitely many children, but the proof may not choose a uniform alphabet or degree bound.
- **Ghost source node:** a node in `F∩U.levelSet(L(j+1))` with no predecessor on the preceding selected level is rejected at the intrinsic-definition boundary.
- **Relative containment:** if the finite intrinsic carrier lies in some infinite `T`, extending by **full ambient cones** generally leaves `T`; apply the verified *relative* extension theorem after absolute realisation rather than claiming the full-cone construction refines `T`.
- **Colouring independence:** the finite object identity is its *carrier*, not different choices of `Fin k` level witnesses.

This is the missing mathematical identification between the source's notation `S_k(U)` and the previous Lean code's realised approximation type. Nothing in this document treats an uncompiled Lean proof as established.
