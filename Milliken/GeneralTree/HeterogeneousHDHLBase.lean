import Milliken.GeneralTree.HeterogeneousDensity

/-!
# Heterogeneous HDHL in one dimension

Todorčević's Chapter 3 one-dimensional highly-dense argument works
for arbitrary pruned locally finitely branching strong trees:
project a highly dense set of unary tuples to the sole coordinate,
obtaining a coordinatewise dense matrix contained in the original set.

No word alphabet, homogeneous tree shape or uniform branching-degree
bound occurs in the proof. This is the genuine heterogeneous base
case for the pending induction on the number of coordinate factors.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Project a subset of the carrier of a unary matrix onto its sole
coordinate. Because the index type is Fin 1, this projection preserves
the entire tuple set without information loss. -/
def heterogeneousUnaryProjection
    (P : Fin 1 → StrongSubtree U)
    (M : HeterogeneousMatrix P)
    (Q : Set (Fin 1 → U))
    (hQM : Q ⊆ M.carrier) : HeterogeneousMatrix P where
  coord := fun _ => {z | ∃ x : Fin 1 → U, x ∈ Q ∧ x 0 = z}
  coord_sub := by
    intro i z hz
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    obtain ⟨x, hxQ, hxz⟩ := hz
    have hnode : x 0 ∈ (P 0).carrier :=
      M.coord_sub 0 ((hQM hxQ) 0)
    rw [hxz] at hnode
    exact hnode

/-- The entire unary projected matrix lies in the original set Q. -/
theorem heterogeneousUnaryProjection_carrier_subset
    (P : Fin 1 → StrongSubtree U)
    (M : HeterogeneousMatrix P)
    (Q : Set (Fin 1 → U))
    (hQM : Q ⊆ M.carrier) :
    (heterogeneousUnaryProjection P M Q hQM).carrier ⊆ Q := by
  intro x hx
  obtain ⟨y, hyQ, hyx⟩ := hx (0 : Fin 1)
  have hxy : x = y := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    exact hyx.symm
  rw [hxy]
  exact hyQ

/-- Product density in a one-coordinate tree becomes coordinatewise
matrix density after projection. -/
theorem heterogeneousUnaryProjection_dense
    (P : Fin 1 → StrongSubtree U)
    (M : HeterogeneousMatrix P)
    (Q : Set (Fin 1 → U))
    (hQM : Q ⊆ M.carrier) {k : ℕ}
    (hQ : HeterogeneousProductDenseAt P Q k) :
    (heterogeneousUnaryProjection P M Q hQM).DenseAt k := by
  intro i z hz
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  let x : HeterogeneousLevelTuple P k :=
    ⟨fun _ => z, by
      intro j
      have hj : j = (0 : Fin 1) := Fin.eq_zero j
      subst j
      exact hz⟩
  obtain ⟨y, hyQ, hxy⟩ := hQ x
  exact ⟨y 0, ⟨y, hyQ, rfl⟩, hxy 0⟩

/-- **Unconditional general-tree HDHL base case:** every highly dense
subset of the unary product of an arbitrary pruned locally finitely
branching strong tree contains a dense matrix of the prescribed scale.
There is no global branching bound or homogeneous alphabet assumption. -/
theorem heterogeneousHDHL_one
    (P : Fin 1 → StrongSubtree U) :
    HasHeterogeneousHDHL P := by
  intro Q hQ k hk
  obtain ⟨n, hn⟩ := hQ k
  let M : HeterogeneousMatrix P :=
    HeterogeneousMatrix.fullLevel P n
  have hM : M.DenseAt n :=
    HeterogeneousMatrix.fullLevel_denseAt P n
  have hproduct :
      HeterogeneousProductDenseAt P (Q ∩ M.carrier) k :=
    hn M hM
  have hsubset : Q ∩ M.carrier ⊆ M.carrier :=
    Set.inter_subset_right
  let N : HeterogeneousMatrix P :=
    heterogeneousUnaryProjection P M (Q ∩ M.carrier) hsubset
  refine ⟨N, ?_, ?_⟩
  · exact heterogeneousUnaryProjection_dense P M
      (Q ∩ M.carrier) hsubset hproduct
  · exact (heterogeneousUnaryProjection_carrier_subset
      P M (Q ∩ M.carrier) hsubset).trans
        Set.inter_subset_left

end GeneralTree
end Milliken
