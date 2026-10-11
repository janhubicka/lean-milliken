import Milliken.GeneralTree.Ancestry

/-!
# Unique strong-tree frontier ancestors and A.3 depth geometry

For a node on a later selected source level there is exactly one
ancestor on each earlier selected level. Uniqueness follows from
the fact that in a rooted tree the predecessors of a fixed node
form a chain, combined with strict increase of ambient ranks.

For a positive-height finite strong approximation lying below
r_d(B) in Todorčević's published finite order (6.3), the
maximal nodes of the approximation lie on B's final selected
level d-1. This precise boundary alignment is needed for the
relative stem graft in A.3; carrier inclusion alone would not
give it.

All statements apply to arbitrary locally finite pruned trees.
They do not assume or establish the general A.3 theorem.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- There is exactly one ancestor of a retained node on each
preceding selected source level. -/
theorem existsUnique_sourceLevel_ancestor
    (S : StrongSubtree U) {n m : ℕ}
    (hnm : n ≤ m) {z : U} (hz : z ∈ S.sourceLevel m) :
    ∃! x : U, x ∈ S.sourceLevel n ∧ x ≤ z := by
  obtain ⟨x, hx, hxz⟩ :=
    S.exists_sourceLevel_ancestor hnm hz
  refine ⟨x, ⟨hx, hxz⟩, ?_⟩
  intro y hy
  rcases le_total_of_directed hxz hy.2 with hyx | hxy
  · exact U.eq_of_le_of_level_eq hyx
      (hy.1.2.trans hx.2.symm)
  · exact (U.eq_of_le_of_level_eq hxy
      (hx.2.trans hy.1.2.symm)).symm

/-- Every retained node at or beyond source level n has a
unique frontier ancestor at level n. -/
theorem existsUnique_frontier_ancestor
    (S : StrongSubtree U) (n : ℕ)
    {z : U} (hz : z ∈ S.carrier)
    (hout : z ∉ S.initialPart n) :
    ∃! x : U, x ∈ S.sourceLevel n ∧ x ≤ z := by
  obtain ⟨m, hm⟩ := S.carrier_levels z hz
  have hnm : n ≤ m := by
    by_contra hnot
    have hmn : m < n := Nat.lt_of_not_ge hnot
    exact hout ⟨hz, m, hmn, hm⟩
  exact S.existsUnique_sourceLevel_ancestor hnm ⟨hz, hm⟩

end StrongSubtree

/-- For any positive source height, the maximal level of a
realized approximation is nonempty. -/
theorem maxLevel_nonempty_succ
    {n : ℕ} (a : SFinite U (n + 1)) :
    (maxLevel a).Nonempty := by
  obtain ⟨S, hS⟩ := a.realised
  obtain ⟨x, hx⟩ := S.sourceLevel_nonempty n
  have ha : r (n + 1) S = a := by
    apply FiniteApprox.ext_carrier
    exact hS.symm
  refine ⟨x, ?_⟩
  rw [← ha, maxLevel_r_succ]
  exact hx

/-- The top of a nonempty finite stem must align with the last
selected level of the larger approximation in the literal
book order (6.3). In particular d is positive. -/
theorem bookLeFin_succ_lastLevel
    {n d : ℕ} (a : SFinite U (n + 1))
    (B : SInfinity U)
    (h : bookLeFin ⟨n + 1, a⟩ ⟨d, r d B⟩) :
    ∃ j : ℕ, d = j + 1 ∧
      maxLevel a ⊆ B.sourceLevel j := by
  cases d with
  | zero =>
      obtain ⟨x, hx⟩ := maxLevel_nonempty_succ a
      have hxB := (bookLeFin_iff.mp h).2 hx
      rw [maxLevel_r_zero] at hxB
      simpa using hxB
  | succ j =>
      refine ⟨j, rfl, ?_⟩
      intro x hx
      have hxB := (bookLeFin_iff.mp h).2 hx
      rwa [maxLevel_r_succ] at hxB

/-- The empty approximation always has source depth zero in
the published finitization. -/
theorem bookDepth_zero_of_empty
    (a : SFinite U 0) (B : SInfinity U) {d : ℕ}
    (hd : (generalBookFinitization U).HasDepth a B d) :
    d = 0 := by
  obtain ⟨S, hS⟩ := r_surjective (U := U) 0 a
  have haB : a = r 0 B :=
    hS.symm.trans (r_zero_eq S B)
  have hle :
      (generalBookFinitization U).leFin
        ⟨0, a⟩
        ((generalApproximationSystem U).finiteApprox 0 B) := by
    change bookLeFin ⟨0, a⟩ ⟨0, r 0 B⟩
    rw [haB]
    exact bookLeFin_refl _
  by_contra hnot
  have hdpos : 0 < d := Nat.pos_of_ne_zero hnot
  exact hd.2 0 hdpos hle

/-- A nonempty stem has positive depth and its top nodes align
with the last source level of B at that depth. -/
theorem bookDepth_succ_lastLevel
    {n d : ℕ} (a : SFinite U (n + 1))
    (B : SInfinity U)
    (hd : (generalBookFinitization U).HasDepth a B d) :
    ∃ j : ℕ, d = j + 1 ∧
      maxLevel a ⊆ B.sourceLevel j :=
  bookLeFin_succ_lastLevel a B hd.1

/-- The height-zero case of A.3(1): every infinite strong tree
realizes the unique empty finite approximation, regardless of
the ambient branching degrees. -/
theorem neighborhood_nonempty_zero
    (a : SFinite U 0) (A : SInfinity U) :
    ((generalApproximationSystem U).neighborhood a A).Nonempty := by
  obtain ⟨S, hS⟩ := r_surjective (U := U) 0 a
  refine ⟨A, ?_⟩
  exact ⟨StrongSubtree.refines_refl A, (r_zero_eq A S).trans hS⟩

end GeneralTree
end Milliken
