import Milliken.GeneralTree.OrderRealization

/-!
# Source-level reindexing of arbitrary strong-tree refinements

If S is a strong subtree of T, every selected ambient level of S
is one of the selected levels of T. Strict monotonicity of the two
level maps yields a unique strictly increasing reindexing function.

This is the general-tree analogue of the common level index map for
homogeneous strong embeddings, requiring no fixed alphabet or
globally bounded branching degree.

The reindexing is needed to protect the first d source levels of
B while grafting tails from a refinement X: all other branches
must be thinned to X's later selected ambient heights.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Index, in the larger strong tree T, of the k-th selected
ambient level of a strong refinement S. -/
noncomputable def refinementIndex
    (S T : StrongSubtree U)
    (hST : S.Refines T) (k : ℕ) : ℕ :=
  Classical.choose (S.selectedLevel_of_refines hST k)

/-- The chosen index reproduces S's actual selected ambient height. -/
theorem levels_refinementIndex
    (S T : StrongSubtree U)
    (hST : S.Refines T) (k : ℕ) :
    S.levels k = T.levels (S.refinementIndex T hST k) :=
  Classical.choose_spec (S.selectedLevel_of_refines hST k)

/-- The index map from selected S levels to selected T levels
is strictly increasing. -/
theorem refinementIndex_strictMono
    (S T : StrongSubtree U)
    (hST : S.Refines T) :
    StrictMono (S.refinementIndex T hST) := by
  intro k l hkl
  apply (T.levels_strictMono.lt_iff_lt).mp
  calc
    T.levels (S.refinementIndex T hST k) =
        S.levels k := (S.levels_refinementIndex T hST k).symm
    _ < S.levels l := S.levels_strictMono hkl
    _ = T.levels (S.refinementIndex T hST l) :=
      S.levels_refinementIndex T hST l

/-- All nodes of S on source level k belong to precisely the
corresponding selected level of T. -/
theorem sourceLevel_subset_refinementIndex
    (S T : StrongSubtree U)
    (hST : S.Refines T) (k : ℕ) :
    S.sourceLevel k ⊆
      T.sourceLevel (S.refinementIndex T hST k) := by
  intro x hx
  refine ⟨hST hx.1, ?_⟩
  exact hx.2.trans (S.levels_refinementIndex T hST k)

/-- A known selected-level inclusion determines the chosen
reindexing uniquely. -/
theorem refinementIndex_eq_of_sourceLevel_subset
    (S T : StrongSubtree U)
    (hST : S.Refines T)
    (k j : ℕ)
    (hin : S.sourceLevel k ⊆ T.sourceLevel j) :
    S.refinementIndex T hST k = j := by
  obtain ⟨x, hx⟩ := S.sourceLevel_nonempty k
  have hindex : T.levels (S.refinementIndex T hST k) =
      T.levels j := by
    calc
      T.levels (S.refinementIndex T hST k) =
          S.levels k := (S.levels_refinementIndex T hST k).symm
      _ = U.level x := hx.2.symm
      _ = T.levels j := (hin hx).2
  exact T.levels_strictMono.injective hindex

/-- Any coordinate of the refinementIndex map lies at least
as far as its input index. This follows because a strictly
increasing map of naturals cannot compress its source levels. -/
theorem le_refinementIndex
    (S T : StrongSubtree U)
    (hST : S.Refines T) (k : ℕ) :
    k ≤ S.refinementIndex T hST k :=
  (S.refinementIndex_strictMono T hST).id_le k

end StrongSubtree
end GeneralTree
end Milliken
