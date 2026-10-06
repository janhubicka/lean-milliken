import Milliken.HalpernLauchli.FinalInduction
import Milliken.HalpernLauchli.MatrixTransport
import Milliken.HalpernLauchli.StabilizationProductLimit

/-!
# Closing the reduced HDHL induction step

Todorčević reduces the successor step to the following statement: if the
complement of `P` contains no somewhere-dense matrix, then `P` contains
a 1-dense matrix.

The stabilization fusion is performed in all `d+1` coordinates.  This is
slightly more symmetric than the notation in the book, but has one useful
formal advantage: all coordinates are reindexed by the same level map.
Consequently "somewhere dense" transports between the pulled-back product
and the ambient product.

The fusion starts from the identity and protects height one, so every limit
embedding fixes the root.  A 1-dense matrix found in the stabilized
pullback therefore maps back to a genuine ambient 1-dense matrix.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Every coordinate of the product stabilization limit fixes the root. -/
theorem productStabilizationLimitFamily_root
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) :
    (productStabilizationLimitFamily hd hHDHL P i).toFun
        ([] : Node ι) = [] := by
  rw [productStabilizationLimit_toFun_eq_stage
    hd hHDHL P 0 i ([] : Node ι) (by simp)]
  rfl

/-- The reduced successor step of HDHL: assuming HDHL in positive
dimension `d`, every subset of a `d+1` product whose complement contains
no somewhere-dense matrix contains a 1-dense matrix. -/
theorem exists_one_dense_of_no_somewhereDense_succ
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    ∃ M : Matrix ι (d + 1),
      M.DenseAt 1 ∧ M.carrier ⊆ P := by
  let F : Fin (d + 1) → StrongEmbedding ι :=
    productStabilizationLimitFamily hd hHDHL P
  let levels : ℕ → ℕ :=
    productStabilizationLimitLevels hd hHDHL P
  let Q : Set (Fin (d + 1) → Node ι) :=
    pullbackProduct F P
  have hF :
      HasCommonLevels F levels := by
    dsimp [F, levels]
    exact productStabilizationLimitFamily_commonLevels
      hd hHDHL P
  have hstab : Stabilized Q := by
    dsimp [Q, F]
    exact productStabilizationLimit_stabilized
      hd hHDHL P
  have hnoQ :
      ¬ ContainsSomewhereDense Qᶜ := by
    dsimp [Q]
    exact no_somewhereDense_compl_pullbackProduct
      (d := d + 1) (by omega)
      F levels hF P hno
  rcases exists_one_dense_of_stabilized
      hd hHDHL hstab hnoQ with
    ⟨M, hMdense, hMsub⟩
  let N : Matrix ι (d + 1) :=
    M.imageUnder F
  refine ⟨N, ?_, ?_⟩
  · dsimp [N]
    apply Matrix.imageUnder_denseAt_one F M
    · intro i
      dsimp [F]
      exact productStabilizationLimitFamily_root
        hd hHDHL P i
    · exact hMdense
  · dsimp [N]
    apply Matrix.imageUnder_carrier_subset_of_pullback
      F M P
    simpa [Q] using hMsub

end HalpernLauchli
end Milliken
