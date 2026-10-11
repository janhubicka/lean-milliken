import Milliken.GeneralTree.MaxLevel

/-!
# Finite index sets for arbitrary local branching

In Todorčević's Chapter 6, the one-step pigeonhole argument colors a
finite product indexed by the ambient children of the last finite strong
level.  These children form a finite set even when the branching degree
is unbounded across the entire ambient tree.

This module exposes a genuine finite indexing *type* for those boundary
nodes, together with a canonical (noncomputable) enumeration by Fin d.
It does not claim the unproved generalized Halpern–Läuchli theorem
for the corresponding possibly non-isomorphic successor cones.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Typed ambient immediate successors of a node, without a global
branching alphabet. -/
abbrev ChildIndex (U : AmbientTree) (x : U) :=
  {y : U // y ∈ U.children x}

instance childIndex_finite (U : AmbientTree) (x : U) :
    Finite (ChildIndex U x) :=
  (U.children_finite x).to_subtype

instance childIndex_nonempty (U : AmbientTree) (x : U) :
    Nonempty (ChildIndex U x) := by
  obtain ⟨y, hy⟩ := U.children_nonempty x
  exact ⟨⟨y, hy⟩⟩

/-- Index type for the finite boundary used by Lemma 6.1 at source
stem height n. For n=0 this is the singleton ambient root, and
for positive n the ambient successors of the last selected level. -/
abbrev BoundaryIndex (S : StrongSubtree U) (n : ℕ) :=
  {x : U // x ∈ S.boundaryAtStem n}

instance boundaryIndex_finite (S : StrongSubtree U) (n : ℕ) :
    Finite (BoundaryIndex S n) :=
  (S.boundaryAtStem_finite n).to_subtype

instance boundaryIndex_nonempty (S : StrongSubtree U) (n : ℕ) :
    Nonempty (BoundaryIndex S n) := by
  obtain ⟨x, hx⟩ := S.boundaryAtStem_nonempty n
  exact ⟨⟨x, hx⟩⟩

noncomputable instance boundaryIndex_fintype (S : StrongSubtree U) (n : ℕ) :
    Fintype (BoundaryIndex S n) :=
  Fintype.ofFinite _

/-- Finite enumeration of the boundary of an arbitrary stem.
The dimension is allowed to grow and is not bounded in U. -/
noncomputable def boundaryEquivFin (S : StrongSubtree U) (n : ℕ) :
    Fin (Fintype.card (BoundaryIndex S n)) ≃ BoundaryIndex S n :=
  (Fintype.equivFin (BoundaryIndex S n)).symm

/-- Every enumerated boundary coordinate is an actual boundary node. -/
theorem boundaryEquivFin_mem (S : StrongSubtree U) (n : ℕ)
    (i : Fin (Fintype.card (BoundaryIndex S n))) :
    ((S.boundaryEquivFin n) i).1 ∈ S.boundaryAtStem n :=
  ((S.boundaryEquivFin n) i).2

end GeneralTree
end Milliken
