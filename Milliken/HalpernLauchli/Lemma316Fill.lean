import Milliken.HalpernLauchli.SparseFiniteHL

/-!
# Completing a cone-dense matrix to a globally dense level matrix

In the color-one contradiction in Lemma 3.16 we have a matrix dense above a
selected base vector.  Property (4) of the tower, however, is stated for a
globally level-dense matrix.  The book silently fills the coordinates outside
the cones above the base.  This file makes that completion explicit.

Inside the base cones we keep the original matrix.  Outside them we put the
whole target level.  Hence any point of the completion which still extends
the base already belonged to the original matrix.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace Matrix

variable {d : ℕ}

/-- Fill the target level outside the coordinate cones above `base`. -/
def fillOutsideAbove
    (M : Matrix ι d) (base : Fin d → Node ι) (l : ℕ) :
    Matrix ι d where
  coord := fun i =>
    M.coord i ∪
      {z : Node ι | z.length = l ∧ ¬ (base i).IsPrefix z}

/-- If the old matrix lies on level `l`, so does the completion. -/
theorem fillOutsideAbove_onLevel
    (M : Matrix ι d) (base : Fin d → Node ι) {l : ℕ}
    (hM : M.OnLevel l) :
    (M.fillOutsideAbove base l).OnLevel l := by
  intro i z hz
  rcases hz with hzM | hzout
  · exact hM i z hzM
  · exact hzout.1

/-- A point of the completion which extends the base in one coordinate came
from the old matrix in that coordinate. -/
theorem mem_of_mem_fillOutsideAbove_of_prefix
    (M : Matrix ι d) (base : Fin d → Node ι) {l : ℕ}
    {i : Fin d} {z : Node ι}
    (hz : z ∈ (M.fillOutsideAbove base l).coord i)
    (hpref : (base i).IsPrefix z) :
    z ∈ M.coord i := by
  rcases hz with hzM | hzout
  · exact hzM
  · exact False.elim (hzout.2 hpref)

/-- The same observation for the whole product carrier. -/
theorem carrier_mem_of_fillOutsideAbove_of_prefix
    (M : Matrix ι d) (base : Fin d → Node ι) {l : ℕ}
    {z : Fin d → Node ι}
    (hz : z ∈ (M.fillOutsideAbove base l).carrier)
    (hpref : ∀ i, (base i).IsPrefix (z i)) :
    z ∈ M.carrier := by
  intro i
  exact M.mem_of_mem_fillOutsideAbove_of_prefix
    base (hz i) (hpref i)

/-- If `M` is dense above `base` at level `n`, its completion on a
later level `l` is globally `n`-dense. -/
theorem fillOutsideAbove_denseAt
    [Nonempty ι]
    (M : Matrix ι d) (base : Fin d → Node ι)
    {n l : ℕ}
    (hM : M.DenseAbove base n)
    (hbase : ∀ i, (base i).length < n)
    (hnl : n ≤ l) :
    (M.fillOutsideAbove base l).DenseAt n := by
  intro i s hs
  by_cases hpref : (base i).IsPrefix s
  · rcases hM i (show s ∈ coneLevel (base i) n from
        ⟨hpref, hs⟩) with
      ⟨y, hyM, hsy⟩
    exact ⟨y, Or.inl hyM, hsy⟩
  · let z : Node ι := extendToLevel s l
    have hsl : s.length ≤ l := by
      rw [hs]
      exact hnl
    have hzlen : z.length = l := by
      dsimp [z]
      exact length_extendToLevel hsl
    have hbasele : (base i).length ≤ s.length := by
      rw [hs]
      exact Nat.le_of_lt (hbase i)
    have hnot : ¬ (base i).IsPrefix z := by
      intro hbz
      apply hpref
      dsimp [z, extendToLevel] at hbz
      exact
        (List.isPrefix_append_of_length
          (l₁ := base i) (l₂ := s)
          (l₃ := List.replicate (l - s.length) (padLetter ι))
          hbasele).mp hbz
    refine ⟨z, ?_, ?_⟩
    · exact Or.inr ⟨hzlen, hnot⟩
    · dsimp [z]
      exact prefix_extendToLevel s l

/-- The completion is a level-dense matrix when the old matrix is itself on
the filling level. -/
theorem fillOutsideAbove_levelDenseAt
    [Nonempty ι]
    (M : Matrix ι d) (base : Fin d → Node ι)
    {n l : ℕ}
    (hLevel : M.OnLevel l)
    (hM : M.DenseAbove base n)
    (hbase : ∀ i, (base i).length < n)
    (hnl : n ≤ l) :
    (M.fillOutsideAbove base l).LevelDenseAt n := by
  exact ⟨l, M.fillOutsideAbove_onLevel base hLevel,
    M.fillOutsideAbove_denseAt base hM hbase hnl⟩

end Matrix

end HalpernLauchli
end Milliken
