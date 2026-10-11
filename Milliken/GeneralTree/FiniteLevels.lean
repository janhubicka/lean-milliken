import Milliken.GeneralTree.Identity

/-!
# Finite ambient levels and finite boundary vectors

For a rooted tree with *locally* finite branching, every ambient level is
finite, even if the degrees are unbounded over the whole tree. This is
the precise finiteness used in Todorčević's Chapter 6, Lemma 6.1:
the immediate-successor boundary of a finite strong-tree stem can
be enumerated by a finite index set.

No global branching alphabet is chosen or assumed.
-/

namespace Milliken

namespace AmbientTree

/-- A rooted tree has exactly one node at ambient level zero. -/
theorem levelSet_zero (U : AmbientTree) :
    U.levelSet 0 = {⊥} := by
  ext x
  constructor
  · intro hx
    change U.level x = 0 at hx
    have heq : (⊥ : U) = x :=
      U.eq_of_le_of_level_eq bot_le
        (by simpa only [U.level_root] using hx.symm)
    exact heq.symm
  · intro hx
    change x = (⊥ : U) at hx
    change U.level x = 0
    rw [hx]
    exact U.level_root

/-- Every node at level n+1 has a predecessor on level n. -/
theorem levelSet_succ_subset_children (U : AmbientTree) (n : ℕ) :
    U.levelSet (n + 1) ⊆
      ⋃ x ∈ U.levelSet n, U.children x := by
  intro y hy
  change U.level y = n + 1 at hy
  have hyne : y ≠ (⊥ : U) := by
    intro hbot
    rw [hbot, U.level_root] at hy
    omega
  have hcov : Order.pred y ⋖ y :=
    Order.pred_covBy_of_not_isMin
      ((not_isMin_iff_ne_bot).mpr hyne)
  have hlevel : U.level (Order.pred y) = n := by
    have hstep := U.level_covBy hcov
    omega
  exact Set.mem_iUnion.mpr
    ⟨Order.pred y, Set.mem_iUnion.mpr ⟨hlevel, hcov⟩⟩

/-- An ambient level is the union of the immediate-successor sets of
nodes at the preceding ambient level. -/
theorem levelSet_succ (U : AmbientTree) (n : ℕ) :
    U.levelSet (n + 1) =
      ⋃ x ∈ U.levelSet n, U.children x := by
  apply Set.Subset.antisymm (U.levelSet_succ_subset_children n)
  intro y hy
  rcases Set.mem_iUnion.mp hy with ⟨x, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨hxlevel, hxy⟩
  have hstep := U.level_covBy hxy
  change U.level y = n + 1
  have hn : U.level x = n := hxlevel
  omega

/-- Every ambient level is finite by finite branching, with no
uniform degree bound. -/
theorem levelSet_finite (U : AmbientTree) (n : ℕ) :
    (U.levelSet n).Finite := by
  induction n with
  | zero =>
      rw [U.levelSet_zero]
      exact Set.finite_singleton _
  | succ n ih =>
      rw [U.levelSet_succ n]
      exact ih.biUnion (fun x hx => U.children_finite x)

/-- A pruned ambient tree has a node at every natural-numbered level. -/
theorem levelSet_nonempty (U : AmbientTree) (n : ℕ) :
    (U.levelSet n).Nonempty := by
  induction n with
  | zero =>
      exact ⟨⊥, U.level_root⟩
  | succ n ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hxy⟩ := U.has_child x
      refine ⟨y, ?_⟩
      change U.level y = n + 1
      have hn : U.level x = n := hx
      have hstep := U.level_covBy hxy
      omega

end AmbientTree

namespace GeneralTree

namespace StrongSubtree

variable {U : AmbientTree}

/-- Every selected level of an infinite strong subtree is finite. -/
theorem sourceLevel_finite (S : StrongSubtree U) (n : ℕ) :
    (S.sourceLevel n).Finite :=
  (U.levelSet_finite (S.levels n)).subset (fun _ hx => hx.2)

/-- Every finite strong-tree approximation has a finite carrier. -/
theorem initialPart_finite (S : StrongSubtree U) (n : ℕ) :
    (S.initialPart n).Finite := by
  induction n with
  | zero =>
      rw [S.initialPart_zero]
      exact Set.finite_empty
  | succ n ih =>
      rw [S.initialPart_succ n]
      exact ih.union (S.sourceLevel_finite n)

/-- Ambient children of the last selected level of a strong tree;
for an n+1 stem, these are the boundary nodes used in Lemma 6.1. -/
def ambientBoundary (S : StrongSubtree U) (n : ℕ) : Set U :=
  {y | ∃ x ∈ S.sourceLevel n, x ⋖ y}

/-- Lemma 6.1's boundary has finitely many coordinates. -/
theorem ambientBoundary_finite (S : StrongSubtree U) (n : ℕ) :
    (S.ambientBoundary n).Finite := by
  have h :
      (⋃ x ∈ S.sourceLevel n, U.children x).Finite :=
    (S.sourceLevel_finite n).biUnion
      (fun x hx => U.children_finite x)
  apply h.subset
  rintro y ⟨x, hx, hxy⟩
  exact Set.mem_iUnion.mpr
    ⟨x, Set.mem_iUnion.mpr ⟨hx, hxy⟩⟩

/-- The boundary is nonempty because the strong subtree has every
source level and the ambient tree has no leaves. -/
theorem ambientBoundary_nonempty (S : StrongSubtree U) (n : ℕ) :
    (S.ambientBoundary n).Nonempty := by
  obtain ⟨x, hx⟩ := S.sourceLevel_nonempty n
  obtain ⟨y, hxy⟩ := U.has_child x
  exact ⟨y, x, hx, hxy⟩

/-- Boundary index set for a stem with n selected levels. At n=0
the book uses the ambient root of U, and at n+1 it uses immediate
ambient successors of the top selected source level of T. -/
def boundaryAtStem (S : StrongSubtree U) : ℕ → Set U
  | 0 => {⊥}
  | n + 1 => S.ambientBoundary n

/-- Finite nonempty indexing set for the common-level product
in Todorčević's A.4 pigeonhole step. -/
theorem boundaryAtStem_finite (S : StrongSubtree U) (n : ℕ) :
    (S.boundaryAtStem n).Finite := by
  cases n with
  | zero =>
      exact Set.finite_singleton _
  | succ n =>
      exact S.ambientBoundary_finite n

theorem boundaryAtStem_nonempty (S : StrongSubtree U) (n : ℕ) :
    (S.boundaryAtStem n).Nonempty := by
  cases n with
  | zero =>
      exact ⟨⊥, rfl⟩
  | succ n =>
      exact S.ambientBoundary_nonempty n

end StrongSubtree

namespace FiniteApprox

variable {U : AmbientTree}

/-- Any realised finite strong subtree of height n has finite carrier. -/
theorem carrier_finite {n : ℕ} (a : FiniteApprox U n) :
    a.carrier.Finite := by
  obtain ⟨S, hS⟩ := a.realised
  rw [hS]
  exact S.initialPart_finite n

end FiniteApprox

end GeneralTree
end Milliken
