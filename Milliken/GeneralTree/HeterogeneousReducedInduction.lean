import Milliken.GeneralTree.HeterogeneousCumulativeStabilization
import Milliken.GeneralTree.HeterogeneousFinalInduction
import Milliken.GeneralTree.HeterogeneousSomewhereDensityBackward

/-!
# The reduced heterogeneous HDHL dimension induction

Assume HDHL for every d-dimensional front family, where d>0.
For a synchronized (d+1)-dimensional product P and a set Q whose
complement contains no somewhere-dense matrix, first construct the
synchronized fully stabilized refinement R given by the checked
cumulative stabilization theorem.

The no-somewhere-dense hypothesis passes from P to R by the
actual-next-frontier coverage theorem. The checked stabilized final
induction then supplies a one-dense matrix in R, in colour Q.

The protected fusion retains the root in every coordinate. The
one-dense matrix in R therefore dominates the entire original
source-level-one frontier of P: each old node has a descendant at
source level one of R, by the proved next-frontier coverage lemma.
The identical coordinate sets thus form a one-dense matrix in P.

No A4, uniform branching bound or same-dimensional HDHL premise
occurs. This is the reduced dimension-induction theorem needed
for the final Remark 3.8 high-density reduction.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The cumulative protected stabilization limit preserves every
root of the original synchronized family. -/
theorem heterogeneousCumulativeProtectedFusion_root_eq
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (i : Fin (d + 1)) :
    ((heterogeneousCumulativeProtectedFusion
      P Q hd L hP hAll).limit i).root =
        (P i).root := by
  let W := heterogeneousCumulativeProtectedFusion
    P Q hd L hP hAll
  have hFirst : W.family 0 i = P i := rfl
  have hApprox : r 1 (W.limit i) = r 1 (P i) := by
    calc
      r 1 (W.limit i) = r 1 (W.family 1 i) :=
        W.limit_approx i 1
      _ = r 1 (W.family 0 i) := W.protects 0 i
      _ = r 1 (P i) := by rw [hFirst]
  have hSource :
      (W.limit i).sourceLevel 0 = (P i).sourceLevel 0 := by
    calc
      (W.limit i).sourceLevel 0 = maxLevel (r 1 (W.limit i)) :=
        (maxLevel_r_succ (W.limit i) 0).symm
      _ = maxLevel (r 1 (P i)) := by rw [hApprox]
      _ = (P i).sourceLevel 0 := maxLevel_r_succ (P i) 0
  have hroot :
      (P i).root ∈ (W.limit i).sourceLevel 0 := by
    rw [hSource]
    exact ⟨(P i).root_mem, (P i).root_level⟩
  rw [(W.limit i).sourceLevel_zero_eq_singleton] at hroot
  exact hroot.symm

/-- **Reduced heterogeneous HDHL induction.**
For synchronized (d+1)-dimensional strong-tree products, the
absence of any somewhere-dense complementary matrix implies
a Q-monochromatic matrix dense above every source-one node,
assuming only HDHL in all d-dimensional front families. -/
theorem heterogeneousReducedHDHL_of_previous
    (P : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (Q : Set (Fin (d + 1) → U))
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ) :
    ∃ B : HeterogeneousMatrix P,
      B.DenseAt 1 ∧ B.carrier ⊆ Q := by
  classical
  let W := heterogeneousCumulativeProtectedFusion
    P Q hd L hP hAll
  let R : Fin (d + 1) → StrongSubtree U := W.limit
  have hStage0 : ∀ i, W.family 0 i = P i := by
    intro i
    rfl
  have hRP : ∀ i, (R i).Refines (P i) := by
    intro i
    have hs := W.limit_refines 0 i
    change (R i).Refines (W.family 0 i) at hs
    rw [hStage0 i] at hs
    exact hs
  have hRlevels : ∀ i, (R i).levels = W.limitLevels :=
    W.limit_levels
  have hRstab : HeterogeneousStabilized R Q :=
    heterogeneousCumulativeProtectedFusion_stabilized
      P Q hd L hP hAll
  have hRno : ¬ HeterogeneousContainsSomewhereDense R Qᶜ :=
    heterogeneousNoSomewhereDense_refinement
      P R (Nat.zero_lt_succ d)
      L W.limitLevels hP hRlevels hRP Q hno
  obtain ⟨M, hMdense, hMsub⟩ :=
    heterogeneousExists_one_dense_of_stabilized
      R Q hd
      (hAll (fun i : Fin d => R i.castSucc))
      hRstab hRno
  let B : HeterogeneousMatrix P := {
    coord := M.coord
    coord_sub := by
      intro i z hz
      exact hRP i (M.coord_sub i hz)
  }
  have hRoot (i : Fin (d + 1)) :
      (R i).root = (P i).root :=
    heterogeneousCumulativeProtectedFusion_root_eq
      P Q hd L hP hAll i
  have hDense : B.DenseAt 1 := by
    intro i x hx
    have hPzero : (P i).root ∈ (P i).sourceLevel 0 :=
      ⟨(P i).root_mem, (P i).root_level⟩
    have hRzero : (P i).root ∈ (R i).sourceLevel 0 := by
      rw [← hRoot i]
      exact ⟨(R i).root_mem, (R i).root_level⟩
    obtain ⟨z, hzR, hxz⟩ :=
      (P i).exists_next_sourceLevel_descendant_of_refines
        (R i) (hRP i) hPzero hRzero hx
        ((P i).root_below x hx.1)
    obtain ⟨y, hyM, hzy⟩ := hMdense i z hzR
    exact ⟨y, hyM, hxz.trans hzy⟩
  refine ⟨B, hDense, ?_⟩
  intro x hx
  exact hMsub hx

end GeneralTree
end Milliken
