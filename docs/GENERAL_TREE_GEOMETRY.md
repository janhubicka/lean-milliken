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
