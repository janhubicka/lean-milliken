import Milliken.GeneralTree.ProductHL
import Milliken.GeneralTree.RefinementLevels

/-!
# Canonical boundary ancestors of strong refinements

If S refines T, every node on the kth source level of S has
a unique ancestor on the kth source level of T.
The kth ambient selected height of S occurs at some later
source index m≥k of T, and the verified unique source-level
ancestor theorem identifies its unique T-boundary node.

The result is the canonical map from one-step extension
representatives to the finite source-boundary cone factors.
In particular, every selected node of a strong refinement
lies in precisely one of the actual successor cones of T.

This lemma is structural; it does not assert Halpern–Läuchli
or the generalized A.4 conclusion.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A selected node of a strong refinement has exactly one
ancestor on the same source index of the larger tree. -/
theorem existsUnique_boundaryAncestor
    (S T : StrongSubtree U)
    (hST : S.Refines T) (n : ℕ)
    {z : U} (hz : z ∈ S.sourceLevel n) :
    ∃! x : U, x ∈ T.sourceLevel n ∧ x ≤ z := by
  have hindex :
      z ∈ T.sourceLevel (S.refinementIndex T hST n) :=
    S.sourceLevel_subset_refinementIndex T hST n hz
  exact T.existsUnique_sourceLevel_ancestor
    (S.le_refinementIndex T hST n) hindex

/-- The unique T-boundary coordinate of one selected S-node. -/
noncomputable def boundaryAncestor
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (z : SourceBoundary S n) :
    SourceBoundary T n := by
  have h := S.existsUnique_boundaryAncestor T hST n z.2
  exact ⟨Classical.choose h, (Classical.choose_spec h).1.1⟩

/-- A boundary node is an actual ambient ancestor of
the selected refinement node mapped to it. -/
theorem boundaryAncestor_le
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (z : SourceBoundary S n) :
    (S.boundaryAncestor T hST n z).1 ≤ z.1 := by
  have h := S.existsUnique_boundaryAncestor T hST n z.2
  exact (Classical.choose_spec h).1.2

/-- Every node on a selected source level of a strong refinement
lies in one of the original T-boundary strong successor cones. -/
theorem sourceLevel_subset_boundaryCones
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) :
    S.sourceLevel n ⊆
      ⋃ i : SourceBoundary T n, (boundaryCones T n i).carrier := by
  intro z hz
  let zS : SourceBoundary S n := ⟨z, hz⟩
  let i : SourceBoundary T n :=
    S.boundaryAncestor T hST n zS
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  exact ⟨hST hz.1, S.boundaryAncestor_le T hST n zS⟩

end StrongSubtree
end GeneralTree
end Milliken
