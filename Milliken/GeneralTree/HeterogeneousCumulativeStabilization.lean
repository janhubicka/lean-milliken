import Milliken.GeneralTree.HeterogeneousStabilizationInheritance
import Milliken.GeneralTree.HeterogeneousStabilizationLimit

/-!
# Cumulative stabilization of heterogeneous tree products

Assuming HDHL for every genuinely heterogeneous front family of
dimension d>0, we iteratively stabilize the (d+1)-product one
last-coordinate selected source level at a time.

At stage n, the first n last-coordinate section levels are
stabilized. The next stage applies the full-product source-n
stabilization lemma, preserves the first n+1 source approximations,
and inherits all older stabilized identities by the checked
protected-refinement theorem.

This produces a synchronized protected fusion sequence. The
independently proved finite-code fusion constructor, with no
use of A4, yields its genuine infinite limit. The checked
stabilization-at-limit theorem upgrades the finite-stage
identities to full heterogeneous stabilization of Q.

The only Ramsey hypothesis below is the *previous-dimension*
HDHL theorem, explicitly passed for all front families. No
unproved HL/A4 axiom or homogeneous branching alphabet occurs.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Cumulative stage: Q is stabilized at every last-coordinate
source level below n, on a synchronized genuine strong-tree
refinement of the original input family. -/
structure HeterogeneousCumulativeStabilizationState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (n : ℕ) where
  family : Fin (d + 1) → StrongSubtree U
  levels : ℕ → ℕ
  synchronized : ∀ i, (family i).levels = levels
  refines : ∀ i, (family i).Refines (P i)
  stabilized : ∀ t, t < n → HeterogeneousStabilizedAt family Q t

/-- Initially there are no last-coordinate source levels to stabilize. -/
def initialHeterogeneousCumulativeStabilizationState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L) :
    HeterogeneousCumulativeStabilizationState P Q 0 where
  family := P
  levels := L
  synchronized := hP
  refines := fun i => StrongSubtree.refines_refl (P i)
  stabilized := by
    intro t ht
    omega

/-- A stabilization step remembers the inclusion and protected
approximation agreement required for a genuine infinite fusion. -/
structure HeterogeneousCumulativeStabilizationStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    {n : ℕ}
    (S : HeterogeneousCumulativeStabilizationState P Q n) where
  next : HeterogeneousCumulativeStabilizationState P Q (n + 1)
  refines : ∀ i, (next.family i).Refines (S.family i)
  protects : ∀ i,
    r (n + 1) (next.family i) = r (n + 1) (S.family i)

/-- One complete cumulative stage, using the previous-dimensional
HDHL theorem and the hereditary stabilization lemma. -/
theorem exists_heterogeneousCumulativeStabilizationStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    {n : ℕ}
    (S : HeterogeneousCumulativeStabilizationState P Q n) :
    Nonempty (HeterogeneousCumulativeStabilizationStep P Q S) := by
  classical
  obtain ⟨M, T, hM, hT, hnew⟩ :=
    exists_heterogeneousStabilizedAt_stage
      S.family hd S.levels S.synchronized hAll Q n
  have hSyn : ∀ i, (T i).levels = M :=
    fun i => (hT i).2.2
  have hSub : ∀ i, (T i).Refines (P i) := by
    intro i
    exact ((hT i).1).trans (S.refines i)
  have hOld :
      ∀ t, t < n + 1 → HeterogeneousStabilizedAt T Q t := by
    intro t ht
    by_cases htn : t < n
    · have hprefix :
          ∀ i, r (t + 2) (T i) = r (t + 2) (S.family i) := by
        intro i
        exact r_coherent_le (T i) (S.family i)
          (n + 1) (hT i).2.1 (t + 2) (by omega)
      exact HeterogeneousStabilizedAt.refinement
        S.family T hd S.levels M
        S.synchronized hSyn (fun i => (hT i).1)
        Q t hprefix (S.stabilized t htn)
    · have htnEq : t = n := by omega
      subst t
      exact hnew
  let next : HeterogeneousCumulativeStabilizationState
      P Q (n + 1) := {
    family := T
    levels := M
    synchronized := hSyn
    refines := hSub
    stabilized := hOld
  }
  exact ⟨⟨next, (fun i => (hT i).1),
    (fun i => (hT i).2.1)⟩⟩

/-- Canonically choose the next stabilized protected stage. -/
noncomputable def nextHeterogeneousCumulativeStabilizationStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    {n : ℕ}
    (S : HeterogeneousCumulativeStabilizationState P Q n) :
    HeterogeneousCumulativeStabilizationStep P Q S :=
  Classical.choice
    (exists_heterogeneousCumulativeStabilizationStep P Q hd hAll S)

/-- Infinite sequence of finite cumulative stabilization stages. -/
noncomputable def heterogeneousCumulativeStabilizationState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R) :
    (n : ℕ) → HeterogeneousCumulativeStabilizationState P Q n
  | 0 => initialHeterogeneousCumulativeStabilizationState P Q L hP
  | n + 1 =>
      (nextHeterogeneousCumulativeStabilizationStep
        P Q hd hAll
        (heterogeneousCumulativeStabilizationState
          P Q hd L hP hAll n)).next

theorem heterogeneousCumulativeStabilizationState_succ_refines
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (n : ℕ) (i : Fin (d + 1)) :
    ((heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll (n + 1)).family i).Refines
    ((heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n).family i) := by
  change
    ((nextHeterogeneousCumulativeStabilizationStep
      P Q hd hAll
      (heterogeneousCumulativeStabilizationState
        P Q hd L hP hAll n)).next.family i).Refines
    ((heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n).family i)
  exact (nextHeterogeneousCumulativeStabilizationStep
    P Q hd hAll
    (heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n)).refines i

theorem heterogeneousCumulativeStabilizationState_succ_protects
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (n : ℕ) (i : Fin (d + 1)) :
    r (n + 1)
      ((heterogeneousCumulativeStabilizationState
        P Q hd L hP hAll (n + 1)).family i) =
    r (n + 1)
      ((heterogeneousCumulativeStabilizationState
        P Q hd L hP hAll n).family i) := by
  change
    r (n + 1)
      ((nextHeterogeneousCumulativeStabilizationStep
        P Q hd hAll
        (heterogeneousCumulativeStabilizationState
          P Q hd L hP hAll n)).next.family i) =
    r (n + 1)
      ((heterogeneousCumulativeStabilizationState
        P Q hd L hP hAll n).family i)
  exact (nextHeterogeneousCumulativeStabilizationStep
    P Q hd hAll
    (heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n)).protects i

/-- The finite stages form a true synchronized fusion sequence. -/
noncomputable def heterogeneousCumulativeProtectedFusion
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R) :
    HeterogeneousProtectedFusion U (d + 1) where
  family := fun n =>
    (heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n).family
  commonLevels := fun n =>
    (heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n).levels
  synchronized := by
    intro n i
    exact (heterogeneousCumulativeStabilizationState
      P Q hd L hP hAll n).synchronized i
  refines := by
    intro n i
    exact heterogeneousCumulativeStabilizationState_succ_refines
      P Q hd L hP hAll n i
  protects := by
    intro n i
    exact heterogeneousCumulativeStabilizationState_succ_protects
      P Q hd L hP hAll n i

/-- The canonical synchronized limit is stabilized at *all*
last-coordinate selected source levels. No extra combinatorial
hypothesis is used beyond front-dimensional HDHL. -/
theorem heterogeneousCumulativeProtectedFusion_stabilized
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R) :
    HeterogeneousStabilized
      (heterogeneousCumulativeProtectedFusion
        P Q hd L hP hAll).limit Q := by
  apply HeterogeneousProtectedFusion.limit_stabilized
  intro n t htn
  exact (heterogeneousCumulativeStabilizationState
    P Q hd L hP hAll n).stabilized t htn

/-- Final stabilization reduction in the heterogeneous HDHL
dimension induction: assuming HDHL for *all* previous-dimensional
families, every synchronized (d+1)-family has a synchronized
strong refinement whose original product set is stabilized. -/
theorem exists_heterogeneousStabilizedRefinement
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R) :
    ∃ (M : ℕ → ℕ) (R : Fin (d + 1) → StrongSubtree U),
      StrictMono M ∧
      (∀ i, (R i).Refines (P i) ∧ (R i).levels = M) ∧
      HeterogeneousStabilized R Q := by
  let W := heterogeneousCumulativeProtectedFusion
    P Q hd L hP hAll
  refine ⟨W.limitLevels, W.limit, W.limitLevels_strictMono
    (Nat.zero_lt_succ d), ?_,
    heterogeneousCumulativeProtectedFusion_stabilized
      P Q hd L hP hAll⟩
  intro i
  have hsub := W.limit_refines 0 i
  change (W.limit i).Refines (P i) at hsub
  exact ⟨hsub, W.limit_levels i⟩

end GeneralTree
end Milliken
