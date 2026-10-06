import Milliken.OneStep

/-!
# Todorčević's Lemma 6.1: the canonical-stem pigeonhole lemma

Assuming the strong-subtree Halpern--Läuchli theorem, every binary coloring
of the one-step extensions of the canonical stem `r_n(T)` is homogeneous
below a refinement in `[n,T]`.

This is the exact Chapter 6 construction: color boundary tuples by the
`(n+1)`st approximation they generate, apply Halpern--Läuchli, graft the
resulting coordinate subtrees onto the fixed stem, and use the factor
parametrization to verify that no one-step extension was missed.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

/-- Canonical-stem form of Todorčević's Lemma 6.1. -/
theorem canonicalPigeonhole_of_boundaryHL
    [Finite ι] [Nonempty ι]
    (hHL : BoundaryHL ι)
    {n : ℕ} (T : StrongEmbedding ι)
    (O : Set (StrongTreeSpace.Approx ι (n + 1))) :
    ∃ S : StrongEmbedding ι,
      S ∈ (StrongTreeSpace.approximationSystem ι).levelNeighborhood n T ∧
        ((StrongTreeSpace.approximationSystem ι).oneStepApproximations
              (StrongTreeSpace.approx ι n T) S ⊆ O ∨
          Disjoint
            ((StrongTreeSpace.approximationSystem ι).oneStepApproximations
              (StrongTreeSpace.approx ι n T) S)
            O) := by
  classical
  rcases hHL n 2 (boundaryColor T O) with
    ⟨color, F, hF, hhom⟩
  let S : StrongEmbedding ι :=
    StrongEmbedding.comp T (BoundaryGraft.graft F hF)
  have hS :
      S ∈ (StrongTreeSpace.approximationSystem ι).levelNeighborhood n T := by
    dsimp [S]
    exact BoundaryGraft.comp_graft_mem_levelNeighborhood T F hF
  refine ⟨S, hS, ?_⟩
  by_cases hc : color = 0
  · left
    intro b hb
    rcases hb with ⟨X, hX, hb⟩
    rcases hX.1 with ⟨H, hfac⟩
    subst X
    have hstem :
        StrongTreeSpace.approx ι n
            (StrongEmbedding.comp S H) =
          StrongTreeSpace.approx ι n T :=
      hX.2
    have hparam := factor_oneStep_eq_tuple
      T F hF H (by simpa [S] using hstem)
    rcases hparam with ⟨k, r, hr, m, hx, heq⟩
    change
      StrongTreeSpace.approx ι (n + 1)
          (StrongEmbedding.comp S H) = b at hb
    have heq' :
        StrongTreeSpace.approx ι (n + 1)
            (StrongEmbedding.comp S H) =
          tupleApprox T (fun q => (F q).toFun (r q)) hx := by
      simpa [S] using heq
    have hbtuple :
        b = tupleApprox T (fun q => (F q).toFun (r q)) hx :=
      hb.symm.trans heq'
    rw [hbtuple]
    apply (boundaryColor_eq_zero_iff
      T O (fun q => (F q).toFun (r q)) hx).1
    exact (hhom k r hr).trans hc
  · right
    apply Set.disjoint_left.2
    intro b hb hO
    rcases hb with ⟨X, hX, hb⟩
    rcases hX.1 with ⟨H, hfac⟩
    subst X
    have hstem :
        StrongTreeSpace.approx ι n
            (StrongEmbedding.comp S H) =
          StrongTreeSpace.approx ι n T :=
      hX.2
    have hparam := factor_oneStep_eq_tuple
      T F hF H (by simpa [S] using hstem)
    rcases hparam with ⟨k, r, hr, m, hx, heq⟩
    change
      StrongTreeSpace.approx ι (n + 1)
          (StrongEmbedding.comp S H) = b at hb
    have heq' :
        StrongTreeSpace.approx ι (n + 1)
            (StrongEmbedding.comp S H) =
          tupleApprox T (fun q => (F q).toFun (r q)) hx := by
      simpa [S] using heq
    have hbtuple :
        b = tupleApprox T (fun q => (F q).toFun (r q)) hx :=
      hb.symm.trans heq'
    have hOtuple :
        tupleApprox T (fun q => (F q).toFun (r q)) hx ∈ O := by
      rw [hbtuple] at hO
      change
        tupleApprox T (fun q => (F q).toFun (r q)) hx ∈ O at hO
      exact hO
    have hzero :
        boundaryColor T O (fun q => (F q).toFun (r q)) = 0 :=
      (boundaryColor_eq_zero_iff
        T O (fun q => (F q).toFun (r q)) hx).2 hOtuple
    have hcolor0 : color = 0 :=
      (hhom k r hr).symm.trans hzero
    exact hc hcolor0

/-- Canonical-stem Lemma 6.1 directly from the standard strong-subtree
Halpern--Läuchli theorem. -/
theorem canonicalPigeonhole_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι)
    {n : ℕ} (T : StrongEmbedding ι)
    (O : Set (StrongTreeSpace.Approx ι (n + 1))) :
    ∃ S : StrongEmbedding ι,
      S ∈ (StrongTreeSpace.approximationSystem ι).levelNeighborhood n T ∧
        ((StrongTreeSpace.approximationSystem ι).oneStepApproximations
              (StrongTreeSpace.approx ι n T) S ⊆ O ∨
          Disjoint
            ((StrongTreeSpace.approximationSystem ι).oneStepApproximations
              (StrongTreeSpace.approx ι n T) S)
            O) :=
  canonicalPigeonhole_of_boundaryHL
    (boundaryHL_of_strongSubtreeHL hHL) T O

end Chapter6
end Milliken
