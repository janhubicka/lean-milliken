import Milliken.GeneralTree.HeterogeneousFillOutside
import Milliken.GeneralTree.HeterogeneousSparseWitness

/-!
# Todorčević Remark 3.8 for heterogeneous, locally finite trees

A highly dense colour class Q admits a cofinal, strictly increasing
selection of common *source indices* such that the complement of Q
contains no matrix dense from one selected source level to any later
selected source level inside a product of cones.

Unlike a fixed-alphabet proof, all source levels are those of the actual
possibly non-isomorphic coordinate strong trees. The proof uses the
already proved heterogeneous density obstruction and completion
operation. No globally bounded branching degree or higher-dimensional
Halpern--Läuchli hypothesis is used.

This is the selected-level reduction needed to turn the stabilized
HDHL induction step into an unconditional higher-dimensional theorem;
the corresponding strong-tree refinement and stabilization fusion
remain separate obligations.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Choose a high-density test scale for one prescribed target
source index. -/
noncomputable def heterogeneousHighlyDenseScale
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) : ℕ :=
  Classical.choose (hQ k)

/-- The chosen test scale witnesses the original highly-dense
property, with no extra matrix-support assumptions. -/
theorem heterogeneousHighlyDenseScale_spec
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ)
    (M : HeterogeneousMatrix P)
    (hM : M.DenseAt (heterogeneousHighlyDenseScale P hQ k)) :
    HeterogeneousProductDenseAt P (Q ∩ M.carrier) k :=
  (Classical.choose_spec (hQ k)) M hM

/-- Select source indices far enough apart to dominate each
previously needed density scale. The source-index sequence
may have unbounded gaps and is independent of ambient degrees. -/
noncomputable def heterogeneousRemark38Levels
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      max (heterogeneousRemark38Levels P hQ k n + 1)
        (max k
          (heterogeneousHighlyDenseScale P hQ
            (heterogeneousRemark38Levels P hQ k n)))

@[simp] theorem heterogeneousRemark38Levels_zero
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) :
    heterogeneousRemark38Levels P hQ k 0 = 0 := rfl

@[simp] theorem heterogeneousRemark38Levels_succ
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k n : ℕ) :
    heterogeneousRemark38Levels P hQ k (n + 1) =
      max (heterogeneousRemark38Levels P hQ k n + 1)
        (max k
          (heterogeneousHighlyDenseScale P hQ
            (heterogeneousRemark38Levels P hQ k n))) := rfl

theorem heterogeneousRemark38Levels_lt_succ
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k n : ℕ) :
    heterogeneousRemark38Levels P hQ k n <
      heterogeneousRemark38Levels P hQ k (n + 1) := by
  rw [heterogeneousRemark38Levels_succ]
  exact (Nat.lt_succ_self _).trans_le
    (Nat.le_max_left _ _)

theorem heterogeneousRemark38Levels_strictMono
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) :
    StrictMono (heterogeneousRemark38Levels P hQ k) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact heterogeneousRemark38Levels_lt_succ P hQ k n

theorem heterogeneousRemark38Levels_target_le_succ
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k n : ℕ) :
    k ≤ heterogeneousRemark38Levels P hQ k (n + 1) := by
  rw [heterogeneousRemark38Levels_succ]
  exact (Nat.le_max_left k _).trans (Nat.le_max_right _ _)

theorem heterogeneousRemark38Levels_scale_le_succ
    (P : Fin d → StrongSubtree U)
    {Q : Set (Fin d → U)}
    (hQ : HeterogeneousHighlyDense P Q)
    (k n : ℕ) :
    heterogeneousHighlyDenseScale P hQ
        (heterogeneousRemark38Levels P hQ k n) ≤
      heterogeneousRemark38Levels P hQ k (n + 1) := by
  rw [heterogeneousRemark38Levels_succ]
  exact (Nat.le_max_right k _).trans (Nat.le_max_right _ _)

/-- Somewhere density in a source-level-selected product can
occur between *any* two different selected source indices. -/
def HeterogeneousRestrictedSomewhereDense
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ)
    (M : HeterogeneousMatrix P) : Prop :=
  ∃ p q : ℕ, p < q ∧
    ∃ base : HeterogeneousLevelTuple P (levels p),
      M.DenseAbove base.1 (levels q)

/-- A product colour class contains a matrix somewhere dense in the
selected-level sense of Todorčević's Remark 3.8. -/
def HeterogeneousContainsRestrictedSomewhereDense
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ)
    (Q : Set (Fin d → U)) : Prop :=
  ∃ M : HeterogeneousMatrix P,
    HeterogeneousRestrictedSomewhereDense P levels M ∧
      M.carrier ⊆ Q

/-- Main heterogeneous Remark 3.8: a sufficiently spaced selection
of source indices excludes every complement matrix dense between
two selected levels, with arbitrary locally finite branching. -/
theorem heterogeneous_no_restricted_compl_of_highlyDense
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U))
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) :
    ¬ HeterogeneousContainsRestrictedSomewhereDense
      P (heterogeneousRemark38Levels P hQ k) Qᶜ := by
  classical
  rintro ⟨M, ⟨p, q, hpq, base, hMdense⟩, hMsub⟩
  let levels : ℕ → ℕ :=
    heterogeneousRemark38Levels P hQ k
  have hmono : StrictMono levels :=
    heterogeneousRemark38Levels_strictMono P hQ k
  have hnextq : levels (p + 1) ≤ levels q :=
    hmono.monotone (Nat.succ_le_of_lt hpq)
  have hprev : levels p ≤ levels (p + 1) :=
    (hmono (Nat.lt_succ_self p)).le
  have hMdenseNext :
      M.DenseAbove base.1 (levels (p + 1)) :=
    M.denseAbove_of_le base.1 hnextq hMdense
  let A : HeterogeneousMatrix P :=
    M.fillOutsideAbove base.1 (levels q)
  have hAdenseNext : A.DenseAt (levels (p + 1)) :=
    M.fillOutsideAbove_denseAt_of_later
      base hprev hnextq hMdenseNext
  have hscale :
      heterogeneousHighlyDenseScale P hQ (levels p) ≤
        levels (p + 1) := by
    dsimp [levels]
    exact heterogeneousRemark38Levels_scale_le_succ P hQ k p
  have hAdense :
      A.DenseAt (heterogeneousHighlyDenseScale P hQ (levels p)) :=
    A.denseAt_of_le hscale hAdenseNext
  have hQprod :
      HeterogeneousProductDenseAt P
        (Q ∩ A.carrier) (levels p) :=
    heterogeneousHighlyDenseScale_spec P hQ (levels p) A hAdense
  obtain ⟨z, hz, hbasez⟩ := hQprod base
  have hzM : z ∈ M.carrier :=
    M.mem_carrier_of_fillOutsideAbove_of_above
      base.1 (levels q) hz.2 hbasez
  exact (hMsub hzM) hz.1

/-- The consecutive-level sparse complement obstruction is
in particular ruled out by the same chosen sequence. -/
theorem heterogeneous_no_sparse_compl_of_highlyDense
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U))
    (hQ : HeterogeneousHighlyDense P Q)
    (k : ℕ) :
    ¬ ∃ M : HeterogeneousMatrix P,
      HeterogeneousSparseSomewhereDense P
        (heterogeneousRemark38Levels P hQ k) M ∧
      M.carrier ⊆ Qᶜ := by
  rintro ⟨M, ⟨p, base, hdense⟩, hMsub⟩
  apply heterogeneous_no_restricted_compl_of_highlyDense
    P Q hQ k
  exact ⟨M, ⟨p, p + 1, Nat.lt_succ_self p, base, hdense⟩,
    hMsub⟩

end GeneralTree
end Milliken
