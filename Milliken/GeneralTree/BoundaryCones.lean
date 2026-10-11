import Milliken.GeneralTree.ConeStrong

/-!
# Finite synchronized successor-cone families for arbitrary-tree A.4

For every strong T and source index n, the chosen T-nodes on
source level n form a finite nonempty index type. Each node
roots a genuine strong successor cone inside U. All these
cone factors use **one common ambient selected-level sequence**
k ↦ T.levels (n+k).

This is the exact finite vector of heterogeneous strong trees
on which the published Halpern–Läuchli theorem acts in the
canonical pigeonhole proof. No uniform branching degree is
assumed, and no HL conclusion is claimed by the definitions.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Typed index of a retained source-level boundary node. -/
abbrev SourceBoundary (T : StrongSubtree U) (n : ℕ) :=
  {x : U // x ∈ T.sourceLevel n}

instance sourceBoundary_finite (T : StrongSubtree U) (n : ℕ) :
    Finite (SourceBoundary T n) :=
  (T.sourceLevel_finite n).to_subtype

instance sourceBoundary_nonempty (T : StrongSubtree U) (n : ℕ) :
    Nonempty (SourceBoundary T n) := by
  obtain ⟨x, hx⟩ := T.sourceLevel_nonempty n
  exact ⟨⟨x, hx⟩⟩

noncomputable instance sourceBoundary_fintype
    (T : StrongSubtree U) (n : ℕ) :
    Fintype (SourceBoundary T n) :=
  Fintype.ofFinite _

/-- Each finite boundary coordinate is a genuine strong
successor cone of T inside the same ambient U. -/
noncomputable def boundaryCones
    (T : StrongSubtree U) (n : ℕ)
    (i : SourceBoundary T n) : StrongSubtree U :=
  T.coneStrong n i.1 i.2

/-- Every factor is an actual strong refinement of T. -/
theorem boundaryCones_refines
    (T : StrongSubtree U) (n : ℕ)
    (i : SourceBoundary T n) :
    (boundaryCones T n i).Refines T :=
  T.coneStrong_refines n i.1 i.2

/-- The root of the ith factor is the selected boundary node. -/
@[simp] theorem boundaryCones_root
    (T : StrongSubtree U) (n : ℕ)
    (i : SourceBoundary T n) :
    (boundaryCones T n i).root = i.1 := rfl

/-- All factors have one and the same selected ambient level sequence. -/
theorem boundaryCones_levels
    (T : StrongSubtree U) (n : ℕ)
    (i : SourceBoundary T n) :
    (boundaryCones T n i).levels =
      (fun k => T.levels (n + k)) := rfl

/-- The kth source level of a factor is precisely the T-nodes
on source level n+k descending from that boundary node. -/
theorem boundaryCones_sourceLevel
    (T : StrongSubtree U) (n : ℕ)
    (i : SourceBoundary T n) (k : ℕ) :
    (boundaryCones T n i).sourceLevel k =
      {z : U | z ∈ T.sourceLevel (n+k) ∧ i.1 ≤ z} :=
  T.coneStrong_sourceLevel n i.1 i.2 k

/-- Distinct boundary roots cannot share a retained descendant.
This holds without any uniform branching-degree restriction. -/
theorem boundaryCones_pairwise_disjoint
    (T : StrongSubtree U) (n : ℕ)
    {i j : SourceBoundary T n} (hij : i ≠ j) :
    Disjoint (boundaryCones T n i).carrier
      (boundaryCones T n j).carrier := by
  apply Set.disjoint_left.mpr
  intro z hiz hjz
  have hxi : i.1 ≤ z := hiz.2
  have hxj : j.1 ≤ z := hjz.2
  have hlevel : U.level i.1 = U.level j.1 :=
    i.2.2.trans j.2.2.symm
  have heq : i.1 = j.1 := by
    rcases le_total_of_directed hxi hxj with hji | hij'
    · exact (U.eq_of_le_of_level_eq hji hlevel.symm).symm
    · exact U.eq_of_le_of_level_eq hij' hlevel
  exact hij (Subtype.ext heq)

end GeneralTree
end Milliken
