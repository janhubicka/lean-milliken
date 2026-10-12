import Milliken.GeneralTree.HeterogeneousAsymmetric

/-!
# Somewhere-dense heterogeneous matrices

A matrix is somewhere dense if, above one finite vector of retained
nodes, it dominates the common selected source level n strictly later
than each base coordinate's own source index.

This is Todorčević's \`SomewhereDense\` definition in the general
locally-finite tree setting, without requiring that the coordinate
roots or source-index positions coincide. It is the notion needed
for the contradiction in heterogeneous Lemma 3.15.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}
variable {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- A common future level dominates every source-level-n node
inside an individually rooted finite product of cones. -/
def SomewhereDense (M : HeterogeneousMatrix P) : Prop :=
  ∃ base : Fin d → U, ∃ n : ℕ,
    (∀ i : Fin d,
      ∃ k : ℕ, k < n ∧ base i ∈ (P i).sourceLevel k) ∧
    M.DenseAbove base n

/-- Density at level one yields a somewhere-dense matrix, with
the actual roots of its heterogeneous factors as base. -/
theorem denseAt_one_somewhereDense
    (M : HeterogeneousMatrix P)
    (hM : M.DenseAt 1) :
    M.SomewhereDense := by
  let root : Fin d → U := fun i => (P i).root
  refine ⟨root, 1, ?_, ?_⟩
  · intro i
    exact ⟨0, by omega,
      ⟨(P i).root_mem, (P i).root_level⟩⟩
  · intro i x hx _
    exact hM i x hx

end HeterogeneousMatrix

/-- A product colour class contains a somewhere-dense matrix. -/
def HeterogeneousContainsSomewhereDense
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U)) : Prop :=
  ∃ M : HeterogeneousMatrix P,
    M.SomewhereDense ∧ M.carrier ⊆ Q

/-- Complementary absence of somewhere-dense matrices forces
high density, by restricting any failed product-density test to
the offending selected level-k vector. -/
theorem heterogeneousHighlyDense_of_no_somewhere
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U))
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ) :
    HeterogeneousHighlyDense P Q := by
  intro k
  refine ⟨k + 1, ?_⟩
  intro M hM x
  by_contra hnot
  let N : HeterogeneousMatrix P := M.restrictAbove x.1
  have hNdense : N.DenseAbove x.1 (k + 1) :=
    M.restrictAbove_denseAbove x.1 (k + 1) hM
  have hSome : N.SomewhereDense := by
    refine ⟨x.1, k + 1, ?_, hNdense⟩
    intro i
    exact ⟨k, by omega, x.2 i⟩
  have hBad : N.carrier ⊆ Qᶜ := by
    intro y hy hQ
    have hyM : y ∈ M.carrier :=
      M.restrictAbove_carrier_subset x.1 hy
    have hxy : ∀ i, x.1 i ≤ y i :=
      fun i => (hy i).2
    exact hnot ⟨y, ⟨hQ, hyM⟩, hxy⟩
  exact hno ⟨N, hSome, hBad⟩

/-- The elementary two-colour somewhere-dense theorem follows
from heterogeneous HDHL in exactly the tested dimension.  No
higher-dimensional HDHL premise is introduced implicitly. -/
theorem heterogeneousBinarySomewhere_of_hdhl
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    (c : (Fin d → U) → Fin 2) :
    ∃ color : Fin 2, ∃ M : HeterogeneousMatrix P,
      M.SomewhereDense ∧
      ∀ x ∈ M.carrier, c x = color := by
  let K0 : Set (Fin d → U) := {x | c x = 0}
  by_cases hbad : HeterogeneousContainsSomewhereDense P K0ᶜ
  · obtain ⟨M, hSome, hSub⟩ := hbad
    refine ⟨1, M, hSome, ?_⟩
    intro x hx
    have hne : c x ≠ (0 : Fin 2) := by
      intro heq
      exact (hSub hx) heq
    apply Fin.eq_of_val_eq
    omega
  · have hhigh : HeterogeneousHighlyDense P K0 :=
      heterogeneousHighlyDense_of_no_somewhere P K0 hbad
    obtain ⟨M, hDense, hSub⟩ := hHDHL K0 hhigh 1 (by omega)
    refine ⟨0, M, M.denseAt_one_somewhereDense hDense, ?_⟩
    intro x hx
    exact hSub hx

end GeneralTree
end Milliken
