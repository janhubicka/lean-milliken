import Milliken.HalpernLauchli.Induction
import Milliken.HalpernLauchli.Asymmetric

/-!
# Finite Halpern--Läuchli (Todorčević, Theorem 3.9)

For a fixed target density `k`, a sufficiently dense finite matrix has the
following asymmetric Ramsey property under every binary coloring: either
color 1 contains a somewhere-dense submatrix, or color 0 contains a
`k`-dense submatrix.

We phrase a coloring by its color-zero set `K0`; only its intersection with
the carrier of the ambient matrix matters.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- The finite Halpern--Läuchli dichotomy in dimension `d`. -/
def FiniteHL (ι : Type u) (d : ℕ) : Prop :=
  ∀ k : ℕ, ∃ l : ℕ, ∀ M : Matrix ι d,
    M.DenseAt l →
    ∀ K0 : Set (Fin d → Node ι),
      (∃ M1 : Matrix ι d,
          M1.SomewhereDense ∧
          M1.carrier ⊆ M.carrier ∩ K0ᶜ) ∨
      (∃ M0 : Matrix ι d,
          M0.DenseAt k ∧
          M0.carrier ⊆ M.carrier ∩ K0)

/-- In dimension one, product density of a subset can be turned into an
actual one-coordinate matrix. -/
theorem exists_unary_matrix_of_productDense
    {P : Set (Fin 1 → Node ι)} {k : ℕ}
    (hP : ProductDenseAt P k) :
    ∃ N : Matrix ι 1,
      N.DenseAt k ∧ N.carrier ⊆ P := by
  let N : Matrix ι 1 := unaryProjection P
  refine ⟨N, unaryProjection_dense hP, ?_⟩
  dsimp [N]
  exact unaryProjection_carrier_subset P

/-- Theorem 3.9 in dimension one.  The sharp elementary bound `l=k+1`
suffices: if color zero is not `k`-dense, a bad level-`k` node exposes
a cone inside color one. -/
theorem finiteHL_one [Nonempty ι] :
    FiniteHL ι 1 := by
  intro k
  refine ⟨k + 1, ?_⟩
  intro M hM K0
  let P : Set (Fin 1 → Node ι) := K0 ∩ M.carrier
  by_cases hP : ProductDenseAt P k
  · right
    rcases exists_unary_matrix_of_productDense hP with
      ⟨N, hNdense, hNsub⟩
    exact ⟨N, hNdense, hNsub⟩
  · left
    rcases exists_bad_levelVector P M hP with
      ⟨x, hxsub⟩
    let N : Matrix ι 1 := M.restrictAbove x.1
    have hbase : ∀ i, (x.1 i).length < k + 1 := by
      intro i
      rw [x.2 i]
      omega
    have hNdense :
        N.DenseAbove x.1 (k + 1) := by
      dsimp [N]
      exact M.restrictAbove_denseAbove x.1 hM hbase
    have hNsome : N.SomewhereDense :=
      ⟨x.1, k + 1, hbase, hNdense⟩
    have hNsubM : N.carrier ⊆ M.carrier :=
      M.restrictAbove_carrier_subset x.1
    have hNsub :
        N.carrier ⊆ M.carrier ∩ K0ᶜ := by
      intro z hz
      refine ⟨hNsubM hz, ?_⟩
      intro hzK0
      exact hxsub hz ⟨hzK0, hNsubM hz⟩
    exact ⟨N, hNsome, hNsub⟩

end HalpernLauchli
end Milliken
