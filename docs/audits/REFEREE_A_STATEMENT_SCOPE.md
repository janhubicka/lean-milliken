# Adversarial referee A — mathematical statement and proof scope

Reviewed: `GeneralTree.lean`, `GeneralTree/Published.lean`,
`GeneralTree/HeterogeneousDensity.lean`,
`GeneralTree/HeterogeneousReducedInduction.lean`,
`GeneralTree/HeterogeneousUniversalMilliken.lean`,
`GeneralTree/Original1979Conditional.lean` and the old
`StrongEmbedding` interface.

This is a **separately framed mathematical review**, not an
attestation from an external human referee.

## Confirmed

1. The final heterogeneous HDHL induction is **universal in the ambient
   tree**, permitting recursive use of the theorem on the fresh
   common-root wedge. A fixed-`U` induction would not be sufficient.
2. The compressed levels are **source indices**, not the original
   ambient heights; the wedge shifts each new compressed level by one.
   The proof explicitly transports both positive density and absence
   of a complementary somewhere-dense matrix.
3. The ambient hypothesis is finite branching **per node**, with
   no uniform bound on branching over all nodes.
4. The `StrongSubtree` data include the no-ghost
   `predecessor_exists` field as well as unique extension in every
   *ambient immediate-child cone*. Dropping that field from the
   published interface is not a harmless simplification.

## Scope caveat: intrinsic versus realised finite strong trees

`FiniteApprox U n` currently has a field
`realised : ∃ S : StrongSubtree U, carrier = S.initialPart n`.
The proved `milliken1979_general_unconditional` colours precisely
this **realised** approximation type.

The usual 1979 statement is phrased with *intrinsic finite strong
subtrees*. The existing extension lemma
`exists_refinement_realising_general` only extends an **already
realised** finite approximation inside an infinite strong tree; it
does **not alone establish** that every intrinsic finite strong tree
can be realised. Prove the intrinsic finite-strong-subtree extension
lemma and an equivalence of the two types before claiming that
particular identification definitionally or bijectively.

This is a statement-scope audit finding, **not** evidence of a false
Lean theorem. No unsafe change to the theorem statement is justified
by the audit.

## Homogeneous specialisation

Mathematically, the `List ι` case follows from the unrestricted
heterogeneous/general-tree theorem. Formally, the old conclusions are
about `StrongEmbedding ι` and the specialised
`StrongTreeSpace.approximationSystem ι`; the new theorem concerns
`GeneralTree.StrongSubtree U` and a different approximation system.
A direct Lean replacement requires a proved correspondence
preserving containment/refinement, source restrictions, colouring
objects and basic neighbourhoods. Deleting the old proof **before**
that equivalence would break its exported applications, rather than
simplify a checked derivation.

## Additional checks before external publication

- Confirm intrinsic finite-to-infinite extension and the precise
  correspondence with Milliken (1979), including the height-zero case.
- Compare the literal `bookLeFin` order (6.3) with the
  neighbourhoods used in the older homogeneous Chapter 6 proof:
  `leFin` and `bookLeFin` are not identical relations.
- Prove the separate synchronized **vector finite-subtree** theorem
  before applying single-tree Milliken to a vector-colouring argument.

**Assessment:** The universal-induction strategy is structurally
faithful; the intrinsic-finite interface and the homogeneous
representation equivalence are important scoped follow-up obligations.
