# General-tree identity and ambient rank (formal proof endpoints)

Source: Todorčević, *Introduction to Ramsey Spaces*, §6.1 (str1–str2),
Theorem 6.2. The ambient hypotheses are encoded in
[`Milliken/AmbientTree.lean`](../Milliken/AmbientTree.lean).

For `U : AmbientTree` (rooted, finitely many immediate children at each
node, and no terminal nodes), the following are **proved without any
global bound on branching degree**:

- `AmbientTree.level_mono`: ancestors cannot have higher ambient rank.
- `AmbientTree.level_covBy`: every immediate successor increases rank
  by exactly one.
- `AmbientTree.level_lt`: proper descendants have strictly higher rank.
- `AmbientTree.eq_of_le_of_level_eq`: equal ranks on a chain force equality.
- `GeneralTree.identityStrongSubtree U`: the full ambient tree, with
  `carrier = Set.univ` and levels `n ↦ n`, is an infinite strong subtree.
- `GeneralTree.sinfinity_nonempty U`: the general strong-subtree space
  has a canonical point.
- `GeneralTree.milliken_zero U`: the trivial height-zero case of the
  unrestricted finite-colour theorem.

These are A.1 and ambient-tree geometry prerequisites, **not** a proof
of general Theorem 6.2. The finite-boundary and level-finiteness
development is stacked separately in PR #12.


## General A.1 coherence (no degree bound)

`GeneralTree.StrongSubtree.initialPart_eq_diff` reconstructs the preceding
stem by deleting the intrinsic maximal level. Combined with
`maxLevel_r_succ`, it yields `GeneralTree.r_prev_eq_of_succ` and
`GeneralTree.r_coherent_le` for all locally finitely branching pruned
ambient trees. `vectorApprox_coherent` is the coordinatewise extension
for synchronized vector strong trees. This is A.1 coherence, **not** A.4.


## A.2 fixed-height lower-finiteness

`GeneralTree.boundedApprox_finite`: for any *finite* ambient carrier
`B`, there are finitely many height-`n` realized strong subtrees with
carrier contained in `B`. The argument uses only finite subsets and
carrier extensionality. `bookLeFin_fixedHeight_lowerFinite` is the
corresponding consequence for Todorčević's literal finite order (6.3).

This proves **fixed-height** lower-finiteness. Full A.2 requires proving
that the heights of all predecessors of a given finite approximation
are bounded. It is not yet certified by this module.


## Full published finite-order lower-finiteness (A.2(1))

`GeneralTree.height_le_ncard_of_subset` uses a distinct witness from
each selected source level to bound the source height of any finite
approximation by the number of ambient nodes in a finite carrier.
Combining it with fixed-height finiteness gives
`GeneralTree.bookLeFin_lowerFinite`: the entire lower cone of any
finite approximation under book relation (6.3) is finite.

The remaining A.2 realization and prefix-compatibility laws, as well
as A.3–A.4, remain open for arbitrary locally finite ambient trees.


## A.2 refinement-order realization

`StrongSubtree.selectedLevel_of_refines` shows that a strong subtree
contained in another aligns every one of its selected ambient levels
with a selected level of the larger tree. Combined with the intrinsic
maximal-level identification and prefix inclusion, this proves
`refines_iff_forall_bookLeFin_r`, precisely A.2(2) for the book order.
The only remaining A.2 clause is prefix compatibility (A.2(3)).


## Published A.2 completed (2026-10-11)

`bookLeFin_prefix_compatible` proves A.2(3) for the literal
published maximal-level order (6.3). The key construction chooses the
selected ambient height of the last level of a nonempty prefix and
reconstructs the corresponding prefix in a realizer of the larger
finite approximation. The empty prefix is treated separately.

`generalBookFinitization U` packages all A.2 clauses, including finite
lower cones (A.2(1)), realization of infinite refinement (A.2(2)),
and prefix compatibility (A.2(3)), into the verified Todorčević
`RamseySpace.Finitization` interface. No global degree bound is used.

**Still unproved:** general A.3 amalgamation, A.4 pigeonhole, closedness,
and the resulting unrestricted topological Milliken theorem.


## A.3 stem/frontier geometry

`StrongSubtree.sourceLevel_zero_eq_singleton` verifies the root
level is a singleton. `exists_sourceLevel_ancestor` constructs
retained ancestors on every earlier selected source level using
`predecessor_exists`. Consequently `exists_frontier_ancestor`
places every node beyond a finite stem above a node of its top
selected frontier. These are prerequisites for relative grafting
and A.3 amalgamation, not proofs of A.3.

## Unique frontier ancestors and published-depth boundaries

`StrongSubtree.existsUnique_sourceLevel_ancestor` shows that
an ancestor on each earlier selected level exists **uniquely**,
using the chain property of ambient predecessors. The corresponding
frontier form is `existsUnique_frontier_ancestor`.

`bookLeFin_succ_lastLevel` and
`bookDepth_succ_lastLevel` align the nonempty stem's last
source level with the ambient height at the published depth in
the larger tree; this is a key input for the A.3 graft.
`bookDepth_zero_of_empty` and `neighborhood_nonempty_zero`
handle the separate empty-stem case.

All are geometric or A.3 base-case results, not general
amalgamation or A.4.
