import Milliken.HalpernLauchli.SelectedLevelDensity
import Milliken.HalpernLauchli.Induction

/-!
# Base case and reduction package for selected-level HDHL

The one-dimensional HDHL argument does not use homogeneity of the branching
alphabet. Once high density is phrased in ambient selected levels, the same
projection proof works verbatim.

This file also packages the precise remaining task for Remark 3.8: proving
selected-level HDHL for every finite-branching selection is enough to recover
ordinary HDHL through the selected-level reduced dichotomy.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- HDHL in dimension one for every selected-level tree. -/
theorem hdhl_one
    (S : Selection) :
    HDHL (ι := ι) S 1 := by
  intro P hP k hk
  rcases hP k with ⟨n, hn⟩
  let M : Matrix ι 1 :=
    Matrix.fullLevel (S.levels n)
  have hM :
      M.DenseAt (S.levels n) := by
    dsimp [M]
    exact Matrix.fullLevel_dense
      (ι := ι) (d := 1) (S.levels n)
  have hQ :
      ProductDenseAt (P ∩ M.carrier) (S.levels k) :=
    hn M hM
  let N : Matrix ι 1 :=
    unaryProjection (P ∩ M.carrier)
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    exact unaryProjection_dense hQ
  · dsimp [N]
    exact (unaryProjection_carrier_subset
      (P ∩ M.carrier)).trans Set.inter_subset_left

end SelectedLevelTree

/-- If HDHL is known for every selected-level compression in dimension d,
then ordinary homogeneous HDHL follows. This is the exact endpoint needed
to finish the source-faithful use of Remark 3.8. -/
theorem hdhl_of_all_selected
    [Finite ι] [Nonempty ι]
    {d : ℕ}
    (hselected :
      ∀ S : SelectedLevelTree.Selection,
        SelectedLevelTree.HDHL (ι := ι) S d) :
    HDHL ι d := by
  apply hdhl_of_restrictedReduced
  intro P hP k
  let S : SelectedLevelTree.Selection :=
    SelectedLevelTree.remark38Selection hP k
  have hred :
      RestrictedReducedDichotomy ι d S.levels :=
    SelectedLevelTree.restrictedReduced_of_hdhl
      S (hselected S)
  simpa [S, SelectedLevelTree.remark38Selection] using hred

end HalpernLauchli
end Milliken
