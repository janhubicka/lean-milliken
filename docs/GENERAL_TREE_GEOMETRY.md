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

## Explicit relative stem-graft carrier

`StrongSubtree.spliceCarrier S T n` retains the first n
source levels of S, plus T-nodes above the n-th selected frontier
of S. `spliceLevels S T n j` uses S's earlier selected levels
and T's levels from j onward. The checked geometric lemmas show
strict level increase under matching frontier levels, exact
agreement on every earlier selected level, exact agreement on
the frontier (when it lies in T), and separation of prefix and
tail by ambient rank.

This is the geometric candidate for A.3(1). Its strongness
and the resulting extension and protected-splice claims remain
to be proved; they are **not** axioms or established theorems.

## Exact source levels and carrier of the graft

`spliceCarrier_level_tail` identifies every tail source level of the
candidate graft with T-nodes in the descendant cones of S's selected
frontier. `spliceCarrier_levels` checks that every candidate node
lies on one selected level of the spliced level map. The root belongs
to the candidate when the retained prefix is nonempty and is below
all graft nodes; T-descendant tails remain tails.

These statements are prerequisites of the genuine strongness
constructor, not an assumption of, or proof of, A.3.

## Selected-level reindexing of a strong refinement

`StrongSubtree.refinementIndex S T hST k` is the unique source-level
index of T at which the k-th selected ambient height of S occurs,
whenever S refines T. Its strict monotonicity is verified, as is
the inclusion `S.sourceLevel k ⊆ T.sourceLevel (refinementIndex k)`.
This requires only local finite branching and no global alphabet.

It prepares the common future level sequence for the protected
B/X-cone graft required by A.3(2). The protected graft and
A.3(2) itself remain separate proof obligations.

## Cone transport for A.3

`AmbientTree.le_of_common_descendant_of_level_le` formalizes the
linear ordering of common ancestors by ambient rank.
`StrongSubtree.spliceTail_ancestor` uses it to prove that selected
T-predecessors at or above the retained frontier cannot leave the
grafted descendant cones. Exact conversions between the candidate
source levels and S/T source levels are exported as
`splice_source_before`, `splice_source_at`, and
`splice_source_after`.

These lemmas are for constructing the positive-height strong graft;
they do not yet establish general A.3 or A.4.

## Arbitrarily long selected successor cones

`exists_sourceLevel_descendant_in_childCone` proves that every
immediate ambient successor cone of a retained node of B
meets each strictly later selected source level of B. The
classically selected `longConeRepresentative` chooses one
such node at any prescribed later source level. Different
ambient child cones yield distinct representatives, proved
by `longConeRepresentative_injective`.

These lemmas allow subsequent thinning to a prescribed
subsequence of selected levels without any global degree bound.
The simultaneous thinning and protected A.3(2) splice
are not yet proved.

## Recursive selected-level thinning data

`StrongSubtree.thinningLevelData B f hf hf0 k` recursively
chooses a set of retained nodes at B's source level f(k),
carrying a *proof of level membership* in its dependent type.
At each successor stage one representative is chosen inside
every ambient child cone of every previously retained node.
The definitions `thinningLevel` and `thinningCarrier` and
the successor recursion law `thinningLevel_succ_iff`
are exported for subsequent strongness verification.

The complete thinning `StrongSubtree` constructor,
preservation of all ambient child cones, and the protected
A.3(2) graft remain to be proved.

## Thinning: predecessor and root clauses

`thinningLevel_nonempty`, `thinningLevel_root_below`,
`thinningLevel_predecessor_exists`, and the carrier-level
identification `thinningCarrier_at_level` verify nonemptiness,
the distinguished root, and the selected-predecessor clause of
the thinning construction. `thinningCarrier_subset` keeps the
entire candidate inside B.

Only the ambient-successor **uniqueness** clause and packaging
as a genuine `StrongSubtree` remain for the thinning operator,
which will then be used in the protected A.3(2) graft.

## The genuine positive-height strong graft

`StrongSubtree.spliceStrong S T n j htop` is an explicit
positive-height strong subtree of the arbitrary ambient U. Its
frontier level n lies on T's source level j; the old prefix
comes from S and the descendant cones after the frontier come
from T.

The theorem separately proves selected-predecessor existence
and ambient-successor uniqueness for the splice, without a global
bound on branching. When the finite S-prefix lies inside T,
`spliceStrong_refines` gives the inclusion into T.

This theorem is the core geometric step of positive-height A.3(1).
The exact finite approximation identity and A.3(1) conclusion
still need proof; A.3(2), A.4 and Milliken remain open.

## Complete arbitrary-tree selected-level thinning

`StrongSubtree.thinStrong B f hf hf0` is a **genuine**
strong subtree of any pruned locally finitely branching B,
with selected ambient levels `B.levels (f k)` for every
strictly increasing source-index map f satisfying f 0=0.
The root and predecessor clauses come from the recursive
thinning levels, and `thinningLevel_successor_unique`
establishes unique next-level representatives in each
ambient immediate-child cone by common-descendant ancestry.

`thinStrong_refines` establishes inclusion into B and
`thinStrong_sourceLevel` identifies its exact source levels.

This is the reusable thinning construction needed to keep
**unused** B-frontier cones on a common sparse sequence while
following X in the **used** cones of the A.3(2) graft. The mixed
protected graft, general A.3(2), A.4 and general Milliken
remain separate proof obligations.

## General-tree A.3(1) (amalgamation nonemptiness)

`StrongSubtree.spliceStrong_approx_succ` proves that the genuine
strong graft exactly preserves the first n+1 source levels, including
the cut at source index zero. With the published A.2 depth
identification, `generalAmalgamation_nonempty` establishes
Todorčević's A.3(1) for arbitrary pruned locally finite ambient
trees using the actual `generalBookFinitization U` and
`generalApproximationSystem U` interfaces.

This is not A.3(2) (protected refinements), A.4, closedness,
or the general Milliken theorem.

## A.3(2) protected-tail confinement (formal endpoint)

`selectedLastLevel_eq_of_r_succ_eq` shows agreement of a
finite nonempty strong stem fixes its final ambient rank.
`refines_of_protected_tail` proves that every further strong
refinement Y of C with this fixed stem lies inside X when
**only the descendant cones of X's last selected stem frontier**
are confined to X. All unused C/B-frontier cones may extend
outside X. This relative formulation is essential: requiring
the entire C-tail to lie in X would generally be incompatible
with preserving B's complete depth-d frontier.
`basicNeighborhood_subset_of_protected_tail` packages the
A.3(2) neighborhood inclusion under the repaired condition.

The remaining task is **constructing** such a protected C
which preserves B's complete depth-d prefix, continues unused
cones freely, and follows X within the used cones. No such
construction is asserted or assumed by these results.

## First ambient child of an ancestor

`AmbientTree.exists_child_le_of_lt` proves that for every proper
ancestor x of z there exists an immediate child of x below z,
by induction on the finite ambient rank. Equal-level successor
cones with a common descendant coincide by
`children_eq_of_common_descendant`. These source-neutral order
lemmas are prerequisites of finite-prefix-preserving thinning,
not an A.3(2) proof in themselves.

## Partition into used and unused frontier cones

`AmbientTree.upwardCones F` is the ambient descendant closure
of a frontier set F. Equal-rank disjoint frontiers have disjoint
upward cones. For every chosen Used subset of B's selected
frontier, `frontier_used_unused_disjoint` and
`frontier_used_unused_union` give an exact disjoint partition
of the descendant cones, and every B-carrier node at or beyond
the selected rank lies in one of them.

This is the separation invariant for the mixed protected A.3(2)
tree: used sectors follow X, unused sectors follow a suitably
thinned B. It is not yet the protected mixed strong-subtree
constructor.

## Actual candidate for the protected mixed cone carrier

`StrongSubtree.mixedCarrier D X j n` retains D's first j
source levels, X nodes in cones above X.sourceLevel n, and
D nodes in the remaining j-th frontier cones. Under the frontier
inclusion X.sourceLevel n ⊆ D.sourceLevel j, it agrees with D
at every earlier selected level and contains the complete
D frontier at level j. Critically,
`mixedCarrier_used_sector_in_X` proves that every node of the
mixed carrier in a used X cone belongs to X, exactly the relative
protection condition for A.3(2).

The candidate still requires a common selected-level sequence,
selected-predecessor and ambient-successor uniqueness proofs to
become a genuine strong subtree. Those statements are not assumed.

## Root and rank structure of the mixed protected carrier

With the future levels of X and D synchronized after their chosen
frontiers, `mixedCarrier_levels` verifies that every mixed node
lies at a selected ambient level of D. The original D-root is in
the mixed carrier and is below every mixed node, even when the
frontier cut is at source level zero. If X and D both refine B,
`mixedCarrier_subset_of_common_refinement` preserves inclusion
in B. Together with the previous exact frontier laws this checks
root and regularity for the final mixed strong-subtree constructor.
Selected-predecessor and unique ambient child-cone clauses remain.

## Mixed protected-cone selected predecessor law

`StrongSubtree.mixedCarrier_predecessor_exists` verifies that
when X and D have synchronized selected ambient levels after the
mixing frontier, every candidate mixed node at source level k+1
has a mixed predecessor at source level k. Before the mixing cut
the proof uses D; afterward it uses X in the used sectors and D
in the unused sectors, with same-cone membership preserved by the
order of common ancestors. This is the actual predecessor clause
of the pending mixed `StrongSubtree` constructor; the unique
ambient child-cone successor law remains to be proved.

## Unique successor cones in the protected mixed carrier

`StrongSubtree.mixedCarrier_level_le` identifies every
candidate mixed source level through the protected frontier
with the corresponding complete D-source level.
`mixedCarrier_successor_unique` verifies precisely one
representative on the next mixed selected level in every ambient
immediate-successor cone. Before the frontier this is D's
successor law; afterward it is X's law in used cones and D's
law in unused cones. Sector confinement excludes competing
representatives from the opposite sector.

Combined with the predecessor, root and selected-level lemmas,
this completes the geometric proof obligations for packaging
the mixed carrier as a genuine strong subtree. The constructor
and resulting A.3(2) implication are next.

## Genuine mixed strong tree preserving used and unused cones

`StrongSubtree.mixedStrong D X j n hfront hlevels` is the
actual strong subtree constructed by combining a background D
with X in the used frontier cones, assuming synchronized future
selected levels and frontier inclusion. It retains D's entire
height-(j+1) finite approximation, so unused D-frontier cones
remain represented. When both D and X refine B, the mixed tree
refines B; all nodes in used X-frontier cones belong to X.

This is the central geometric construction for A.3(2). The
remaining application is to choose the background D by
prefix-preserving thinning of B on the common protected-index
schedule, and then invoke the already proved relative
neighborhood-confinement lemma.
