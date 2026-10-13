# Adversarial referee C — unnecessary code and public API

Reviewed: imports in the two umbrella modules,
`Applications/FiniteColour.lean`,
`Original1979Conditional.lean`,
`FixedStemUnconditional.lean`,
`MillikenTheorem.lean`, `BranchEmbedding.lean`,
`Tree.lean`, and the universal heterogeneous theorem.

This is a separately framed maintainability/API review pass, **not**
an assertion that a separate human reviewer signed off.

## Size and dependency issue

At baseline `main` commit `4d23ea85`, the repository has
**225 Lean files** and about **1.30 MB** of Lean text.
It contains two historically developed proof routes for Milliken:

1. A homogeneous `StrongEmbedding ι` route from the
   Hales--Jewett bridge, ending in `Chapter6.milliken` and
   `Applications.milliken1979_homogeneous`.
2. An unrestricted `GeneralTree.StrongSubtree U` route from
   heterogeneous HDHL, ending in `generalMilliken_unconditional`
   and `milliken1979_general_unconditional`.

The old general-tree import chain needlessly passed through route 1
via the *generic* theorem
`RamseySpace.finiteApproximationColouring_for_Milliken`, which had
been defined inside `Applications/FiniteColour.lean`.

## Safe simplification implemented

Extract the generic finite-colouring theorem to
`Milliken/FiniteColourRamseySpace.lean` and change
`Original1979Conditional` and `FixedStemUnconditional` to import
this module. The old homogeneous file now imports this generic file
instead of duplicating its proof.

This preserves **all original declaration names** and avoids the old
homogeneous theorem as a transitive logical dependency of the
unrestricted general-tree theorem.

## Additional candidates, ranked by safety

**Safe next step:** Both `Milliken.lean` and
`Milliken/Applications.lean` explicitly import numerous modules
already imported by other direct imports. Compute transitive
redundancy and remove only demonstrably redundant *import statements*.
Keep the original overall public import closure. Do not delete the
underlying theorem modules merely because a direct import is redundant.

**Requires an API bridge:** Replace homogeneous terminal theorem
proofs with general-tree corollaries after constructing
`List ι` as an `AmbientTree` and an equivalence from the old
`StrongEmbedding` Ramsey-space structures to the new
`GeneralTree.StrongSubtree`/finite approximation structures.
Then preserve old theorem names as very short forwarders.

**Potentially destructive:** Removing `HalpernLauchli/*` proof modules,
Chapter 6, or `StrongEmbedding` outright without the correspondence.
These have independent downstream consumers and offer an independent
proof route; the existing general theorem does not justify a blind
deletion from the *formal* dependency/API graph.

**Do not delete:** GeneralTree boundary grafting, finite-depth
amalgamation, stabilization, compressed-source ancestor lemmas, or
the wedge geometry. They contribute necessary proof obligations or
serve as published-source application interfaces.

## Refactoring outcome (verified by graph analysis; Lean CI follows)

A recursive import-graph analysis found that:
- `Milliken.lean` had **87 direct imports**, of which **78** were
  transitively available from other direct imports.
- `Milliken/Applications.lean` had **131 direct imports**, of which
  **121** were similarly redundant.

All **199 unnecessary direct import statements** were removed,
leaving **9** and **10** direct imports respectively. This preserves
the transitive public import closure by construction: an import was
deleted only when another retained import transitively reaches it.

This is a source/API cleanup, not deletion of the underlying theorem
files or their proofs. Removing the homogeneous implementation itself
still requires the representation bridge detailed above.

## Criterion for deleting old files

A proposed deletion must satisfy: (i) replacement of the old
homogeneous theorem and its application aliases, (ii) no changed
public theorem types, (iii) no broken downstream pinned imports,
(iv) unchanged whole-library theorem/axiom audit, and (v) a genuine
reduction in the set of reachable implementation modules.

**Assessment:** The generic extraction is an immediate nontrivial
simplification. Removing the old homogeneous proof itself is a
follow-up formal equivalence task, not just a code-cleanup command.
