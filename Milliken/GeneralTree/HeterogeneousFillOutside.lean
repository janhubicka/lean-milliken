import Milliken.GeneralTree.HeterogeneousTruncation
import Milliken.GeneralTree.SpliceCones

/-!
# Completion of a heterogeneous cone-dense matrix at its support level

Todorčević's Lemma 3.16 fills an n-dense matrix in the cones above a
finite source-level base with *all* nodes outside those cones on its
later supporting level l. The resulting matrix is globally n-dense,
remains supported on l, and contains no new vectors above the base.

The usual word/prefix proof only needs ancestry and unique source
levels, so it works for arbitrary locally finite strong-tree factors
without any uniform degree bound.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ} {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- Filling at l preserves exact l-level support. -/
theorem fillOutsideAbove_onLevel
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {l : ℕ}
    (hM : M.OnLevel l) :
    (M.fillOutsideAbove base l).OnLevel l := by
  intro i z hz
  rcases hz with hzM | hzout
  · exact hM i z hzM
  · exact hzout.1

/-- If n≤l, a cone-dense matrix becomes globally source-n-dense
by adding selected level-l nodes outside the fixed base cones.
Here the base belongs to a common source level j≤n. -/
theorem fillOutsideAbove_denseAt_of_later
    (M : HeterogeneousMatrix P)
    {j n l : ℕ}
    (base : HeterogeneousLevelTuple P j)
    (hjn : j ≤ n)
    (hnl : n ≤ l)
    (hM : M.DenseAbove base.1 n) :
    (M.fillOutsideAbove base.1 l).DenseAt n := by
  intro i x hx
  by_cases hbase : base.1 i ≤ x
  · obtain ⟨y, hy, hxy⟩ := hM i x hx hbase
    exact ⟨y, Or.inl hy, hxy⟩
  · obtain ⟨z, hz, hxz⟩ :=
      (P i).exists_sourceLevel_descendant hnl hx
    have hnot : ¬ base.1 i ≤ z := by
      intro hbz
      have hrank : U.level (base.1 i) ≤ U.level x := by
        calc
          U.level (base.1 i) = (P i).levels j :=
            (base.2 i).2
          _ ≤ (P i).levels n :=
            (P i).levels_strictMono.monotone hjn
          _ = U.level x := hx.2.symm
      exact hbase
        (U.le_of_common_descendant_of_level_le hbz hxz hrank)
    exact ⟨z, Or.inr ⟨hz, hnot⟩, hxz⟩

/-- Level-supported form required by the section-goodness
hypothesis of the heterogeneous Lemma 3.16 tower. -/
theorem fillOutsideAbove_levelDenseAt_of_later
    (M : HeterogeneousMatrix P)
    {j n l : ℕ}
    (base : HeterogeneousLevelTuple P j)
    (hjn : j ≤ n)
    (hnl : n ≤ l)
    (hLevel : M.OnLevel l)
    (hM : M.DenseAbove base.1 n) :
    (M.fillOutsideAbove base.1 l).LevelDenseAt n := by
  exact ⟨l,
    M.fillOutsideAbove_onLevel base.1 hLevel,
    M.fillOutsideAbove_denseAt_of_later base hjn hnl hM⟩

end HeterogeneousMatrix
end GeneralTree
end Milliken
