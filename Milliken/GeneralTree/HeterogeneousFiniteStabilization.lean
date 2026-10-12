import Milliken.GeneralTree.HeterogeneousLocalConstancyPersistence
import Milliken.GeneralTree.ProtectedBoundaryLift

/-!
# Finite fusion of local heterogeneous stabilization requirements

Fix one common source index n, a synchronized family of arbitrary
locally finitely branching strong trees P, and a *finite* list of
requirements (A, base). Here A is an arbitrary product colour class
and base is an original source-n product boundary tuple.

At each step, lift the new requirement's original boundary tuple
to the current source-n level, use the proved front-dimensional
local-cone stabilization theorem, and retain all previously solved
requirements. Those earlier bases lift to the next source-n level,
and their cone constancy persists through the synchronized
refinement by the common source-index comparison theorem.

The output retains the first n source levels of every input tree,
has a common strictly increasing selected ambient level map, and
satisfies every listed requirement on a suitable descendant
of its original base.

No global branching bound, uniform alphabet, HDHL in a larger
dimension, or additional combinatorial axiom is used. The
infinite stabilization fusion and final HDHL induction remain
separate steps.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- One boundary tuple and the product colour set whose membership
is to be made constant on that boundary cone. -/
structure HeterogeneousLocalRequirement
    (P : Fin d → StrongSubtree U) (n : ℕ) where
  A : Set (Fin d → U)
  base : HeterogeneousLevelTuple P n

/-- Cumulative state after finitely many local requirements have
been solved on an actual synchronized strong-tree family. -/
structure HeterogeneousFiniteStabilizationState
    (P : Fin d → StrongSubtree U) (n : ℕ)
    (requirements : List (HeterogeneousLocalRequirement P n)) where
  S : Fin d → StrongSubtree U
  levels : ℕ → ℕ
  synchronized : ∀ i, (S i).levels = levels
  refines : ∀ i, (S i).Refines (P i)
  prefix_eq : ∀ i, r n (S i) = r n (P i)
  satisfies : ∀ requirement ∈ requirements,
    ∃ b : HeterogeneousLevelTuple S n,
      (∀ i, requirement.base.1 i ≤ b.1 i) ∧
      HeterogeneousConeConstant S requirement.A b

/-- The initial state has no requirements: it is the identity
family with the given common ambient level sequence. -/
def initialHeterogeneousFiniteStabilizationState
    (P : Fin d → StrongSubtree U)
    (n : ℕ) (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L) :
    HeterogeneousFiniteStabilizationState P n [] where
  S := P
  levels := L
  synchronized := hP
  refines := fun i => StrongSubtree.refines_refl (P i)
  prefix_eq := fun _ => rfl
  satisfies := by
    intro requirement hmem
    simp at hmem

/-- Add one local cone-stabilization requirement to the
already solved finite list, preserving *all* earlier requirements
even though their boundary bases can move to later selected levels. -/
theorem exists_heterogeneousFiniteStabilizationStep
    (P : Fin d → StrongSubtree U)
    (n : ℕ) (hd : 0 < d)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    {requirements : List (HeterogeneousLocalRequirement P n)}
    (S : HeterogeneousFiniteStabilizationState P n requirements)
    (requirement : HeterogeneousLocalRequirement P n) :
    Nonempty
      (HeterogeneousFiniteStabilizationState
        P n (requirement :: requirements)) := by
  classical
  obtain ⟨base, hbase⟩ :=
    exists_heterogeneousBoundaryTuple_lift
      P S.S n S.refines S.prefix_eq requirement.base
  obtain ⟨L', T, b', hL', hT, hnext, hconst⟩ :=
    exists_heterogeneousLocalConeStabilization
      S.S hd n base S.levels S.synchronized hAll requirement.A
  have hTP : ∀ i, (T i).Refines (P i) := by
    intro i
    exact ((hT i).1).trans (S.refines i)
  have hprefix : ∀ i, r n (T i) = r n (P i) := by
    intro i
    exact ((hT i).2.1).trans (S.prefix_eq i)
  have hTlevels : ∀ i, (T i).levels = L' :=
    fun i => (hT i).2.2
  refine ⟨{
    S := T
    levels := L'
    synchronized := hTlevels
    refines := hTP
    prefix_eq := hprefix
    satisfies := ?_
  }⟩
  intro R hmem
  rcases List.mem_cons.mp hmem with hnew | hold
  · subst R
    refine ⟨b', ?_, hconst⟩
    intro i
    exact (hbase i).trans (hnext i)
  · obtain ⟨oldbase, holdbase, holdconst⟩ :=
      S.satisfies R hold
    obtain ⟨lifted, hOldLift⟩ :=
      exists_heterogeneousBoundaryTuple_lift
        S.S T n
        (fun i => (hT i).1)
        (fun i => (hT i).2.1)
        oldbase
    have hpreserved : HeterogeneousConeConstant T R.A lifted :=
      HeterogeneousConeConstant.refinement
        S.S T hd S.levels L'
        S.synchronized hTlevels
        (fun i => (hT i).1)
        R.A oldbase holdconst lifted hOldLift
    refine ⟨lifted, ?_, hpreserved⟩
    intro i
    exact (holdbase i).trans (hOldLift i)

/-- All requirements in any finite list can be realized
simultaneously on one synchronized family of genuine
heterogeneous strong refinements, preserving the first n
source levels. -/
theorem exists_heterogeneousFiniteStabilization
    (P : Fin d → StrongSubtree U)
    (n : ℕ) (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (requirements : List (HeterogeneousLocalRequirement P n)) :
    Nonempty
      (HeterogeneousFiniteStabilizationState
        P n requirements) := by
  induction requirements with
  | nil =>
      exact ⟨initialHeterogeneousFiniteStabilizationState
        P n L hP⟩
  | cons requirement rest ih =>
      obtain ⟨S⟩ := ih
      exact exists_heterogeneousFiniteStabilizationStep
        P n hd hAll S requirement

end GeneralTree
end Milliken
