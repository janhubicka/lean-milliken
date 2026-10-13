# Final heterogeneous Milliken reduction: complete proof interface

Status (13 October 2026): **All steps of the reduction are now
Lean-checked and merged.** The universal HDHL theorem and unrestricted
general-tree topological/1979 finite-colour Milliken endpoints are
in `Milliken/GeneralTree/HeterogeneousUniversalMilliken.lean`.
PRs #131–#138 build the wedge, prove transport of both density and
complementary obstructions, and close the dimension induction.
The final proof's `#print axioms` report is part of the 517-endpoint
CI audit and contains only standard Lean axioms.

The stronger *synchronized-vector finite-strong-subtree colouring*
property used by certain applications remains a distinct open theorem.
The body below records the mathematical proof plan that was formally
realised, with references to the verified declarations.

The arbitrary pruned locally finitely branching case does **not** assume
a uniform degree bound. Different factor trees may have different
roots, degree sequences and level maps.


## Verified declaration map

| Proof stage | Checked Lean declaration |
| --- | --- |
| Full compressed ambient levels | `CompressedSourceSelection.compressedAmbient_level_eq_index` |
| Common-root heterogeneous wedge | `WedgeNode.ambientTree` |
| Shifted wedge ambient heights | `WedgeNode.ambient_level_embed` |
| Synchronized true strong subtrees | `WedgeNode.componentStrong`, `WedgeNode.componentStrong_levels` |
| Positive matrix transport | `HeterogeneousCompressionWedge.decodeMatrix_original_denseAt`, `decodeMatrix_original_subset` |
| Complementary obstruction transport | `HeterogeneousCompressionWedge.no_wedge_complement_somewhereDense` |
| Selected-level reduced dichotomy | `heterogeneousRestrictedReduced_of_previous_universal` |
| All-dimensional HDHL | `universalHeterogeneousHDHL` |
| Arbitrary-tree Milliken (topological) | `generalMilliken_unconditional` |
| Original finite-colour Milliken | `milliken1979_general_unconditional` |

The universal induction is quantified over **all** ambients; otherwise
its recursive call at the newly built wedge would be ill-typed.

## Checked dependencies

The main branch contains the following Lean-checked constituents:

- `heterogeneousHDHL_one`: unconditional dimension-one HDHL
  (`HeterogeneousHDHLBase`).
- `heterogeneousReducedHDHL_of_previous`: reduced HDHL for a
  synchronized family of `d+1` strong trees, from HDHL in **all**
  `d`-dimensional families over the same ambient
  (`HeterogeneousReducedInduction`). The complement must have no
  *ordinary* somewhere-dense matrix.
- `heterogeneous_no_restricted_compl_of_highlyDense`:
  Remark 3.8, choosing a strictly increasing sequence `f` with
  `f 0 = 0` and excluding complementary somewhere-dense matrices
  **between levels `f p` and `f q`**.
- `heterogeneousHDHL_of_restrictedReduced`: an exact implication
  from the reduced dichotomy for the selected sequence to full HDHL.
- Full selected-level compressed node sets `Node S f`, with order,
  parent, greatest common ancestor, locally finite `AmbientTree`,
  and exact compressed height. These are the contents of
  PRs #123–#127. **All** old source nodes at each selected index
  `f n` remain; no thinning occurs.
- `heterogeneousSomewhereDense_iff_restricted_id`:
  aligns bases with different source ranks to a common penultimate
  rank (PR #128).
- `HeterogeneousCompressedMatrix.original_denseAt`,
  `original_restricted_somewhereDense`, and
  `no_compressed_complement`:
  transfer density and complementary obstruction back from the
  full compressed product (PR #129).

The published topological and finite-colour conclusions already
follow from universal HDHL by
`generalMilliken_of_all_heterogeneousHDHL` and
`milliken1979_of_all_heterogeneousHDHL`.

## Verified geometric realisation: one ambient for the factors

Let `U : AmbientTree`, `d > 0`,
`P : Fin d → StrongSubtree U`, and
`f : CompressedSourceSelection`. For each `i : Fin d`, let

```text
Tᵢ := CompressedSourceSelection.compressedAmbientTree (P i) f
```

The carrier of `Tᵢ` is the disjoint union of the complete old
source levels `(P i).sourceLevel (f n)`, indexed by `n`.
Each old source node retains **exactly one** compressed copy.
Node `(n,x)` has new ambient height `n`, not old height
`(P i).levels (f n)`.

The types of the `Tᵢ` depend on `i`, so it is **incorrect** to
feed `fun i => identityStrongSubtree Tᵢ` directly to
`heterogeneousReducedHDHL_of_previous`: that theorem needs a
single common ambient type.

Build an explicit forest-with-new-root `W`:

```text
     node of W := ★ | (i, t),   i : Fin d, t : Tᵢ
     ★ ≤ w    := True
     (i,x) ≤ (j,y) := (i = j and x ≤ y)
     height(★) := 0
     height(i,x) := 1 + height_Tᵢ(x)
```

The meet of nodes with different tags is `★`. Within one tag,
the meet and parent are those of `Tᵢ`; each root `(i,⊥)`
has new parent `★`. The new root has exactly `d` children.
All other children are the finite sets of children in the
respective `Tᵢ`, which are nonempty. Thus `W` is an
`AmbientTree` with finite, but not necessarily bounded, degrees.

For each `i`, let `R i : StrongSubtree W` have exactly the
nodes with tag `i`, root `(i,⊥)`, and selected ambient levels

```text
     (R i).levels n = n + 1.
```

**Important:** `R i` is strong in `W` because every next
ambient child inside component `i` belongs to it. It is not
asserted to be a strong subtree of the original `U`.
The family `R` is genuinely synchronized.

Required interface of this construction:

```lean
-- Schematic declarations; these have NOT yet been implemented.
W : AmbientTree
R : Fin d → StrongSubtree W
hR : ∀ i, (R i).levels = fun n => n + 1
embed : (i : Fin d) → Node (P i) f → W
embed_carrier : ∀ i z, embed i z ∈ (R i).carrier
embed_sourceLevel : ∀ i n (z : NodeAt (P i) f n),
  embed i ⟨n,z⟩ ∈ (R i).sourceLevel n
embed_sourceLevel_surj : ∀ i n (w : W),
  w ∈ (R i).sourceLevel n →
    ∃ z : NodeAt (P i) f n, embed i ⟨n,z⟩ = w
embed_order : ∀ i (x y : Node (P i) f),
  embed i x ≤ embed i y ↔ x ≤ y
```

The code above is **schematic** and uses mnemonic names, not literal
Lean exports. The actual implementation is in
`HeterogeneousWedgeOrder`, `HeterogeneousWedgePred`,
`HeterogeneousWedgeAmbient`, `HeterogeneousWedgeHeights`,
`HeterogeneousWedgeComponentCones` and
`HeterogeneousWedgeCompressionTransport`.
Use those modules' checked declarations instead of the schematic identifiers.

## Verified restricted reduced dichotomy by universal dimension induction

Prove, by induction on `d > 0`, the *universal* statement

```lean
-- Schematic target; proved by GeneralTree.universalHeterogeneousHDHL.
∀ (U : AmbientTree) (P : Fin d → StrongSubtree U),
  HasHeterogeneousHDHL P
```

The induction is over **all ambients**, rather than for one fixed
`U`: the induction step changes the ambient from `U` to
the forest `W`.

**Dimension one.** Apply `heterogeneousHDHL_one`.

**Dimension `d+1`, `d > 0`.** Fix any `P` and the selected
sequence `f` supplied by Remark 3.8. Construct `W` and `R`
for its `d+1` coordinates. Lift a colour class
`Q ⊆ (Fin (d+1) → U)` to `Q_W` on tuples in `W` by
reading the unique `i`-tagged compressed node in coordinate
`i`, then decoding its old source node, and testing membership
in `Q`. On tuples not belonging to the corresponding product of
tagged components, the value of `Q_W` can be chosen arbitrarily.

Assume the complement of `Q` contains no restricted
somewhere-dense matrix between selected source indices
`f p < f q`.

1. If the complement of `Q_W` contained an **ordinary**
   somewhere-dense matrix `N` in the product `R`, its
   base coordinates might initially be at different compressed
   source indices `k_i < n`.
2. Choose a descendant of each base at common compressed
   index `p = n-1`. All such descendants exist; density
   above the original base implies density above this vector
   at target index `n`. The existence of `n > 0` uses
   the positive dimension.
3. Pull `N` back along the component embeddings to a
   `HeterogeneousCompressedMatrix P f`. The exact
   source-level and order correspondence in the realization
   turns ordinary density in `R` into the
   `SomewhereDense` condition for that compressed matrix.
4. By `original_restricted_somewhereDense` and
   `original_carrier_subset`, the complementary matrix in
   the original product would be restricted somewhere dense
   between indices `f p` and `f n`. Contradiction.

Therefore `Q_Wᶜ` contains no ordinary somewhere-dense
matrix in the synchronized family `R`. The induction
hypothesis supplies `HasHeterogeneousHDHL` for every
`d`-dimensional family over the **new** ambient `W`.
Apply the already checked
`heterogeneousReducedHDHL_of_previous` to `R` and
`Q_W`.

It yields a matrix dense at compressed source level **one**
and monochromatic for `Q_W`. Pull it back from `W`
to the full compressed matrix, then decode with
`original_denseAt` and `original_carrier_subset`.
The resulting original matrix is dense at
`f.indices 1` and contained in `Q`. This proves
`HeterogeneousRestrictedReducedDichotomy P f.indices`
for the prescribed selection.

Use
`heterogeneousHDHL_of_restrictedReduced` together with
Remark 3.8 to finish the dimension induction, and finally
apply `generalMilliken_of_all_heterogeneousHDHL`
and `milliken1979_of_all_heterogeneousHDHL`.

## Referee checklist before claiming completion

- Never identify the full compressed source tree with a strong
  thinning of the old ambient. The successor multiplicities differ.
- The wedge components must have a common ambient type. A
  type-dependent family of separate `AmbientTree` objects is not
  enough for the existing reduced induction.
- Preserve all full `NodeAt` frontiers when transporting
  `DenseAt`. Subsets or arbitrary representatives are insufficient.
- The original tree may have unbounded local degrees, but every
  single level and each child set is finite; all proofs must use
  only local finiteness.
- Match selected **source** indices `f n`, never substitute
  original ambient heights `P.levels (f n)`.
- For the somewhere-dense contradiction, first move varying
  coordinate base depths to a common penultimate depth.
- Verify the **global** induction hypothesis for the newly
  constructed ambient `W`, not merely for the original `U`.
- Add `#print axioms` for the new unconditional HDHL and Milliken
  endpoints. No `sorryAx`, new axioms, or unproved instance.
- Separately verify that the original finite strong-subtree
  formulation has the necessary realizability/extension interface;
  do not conflate it with the topological approximation formulation.

**Completed:** The single-ambient wedge, matrix comparison, negative
obstruction transport, and universal induction have all passed Lean.
`generalMilliken_unconditional` and
`milliken1979_general_unconditional` are the resulting unconditional
general-tree endpoints. No extra Ramsey principle is assumed.
