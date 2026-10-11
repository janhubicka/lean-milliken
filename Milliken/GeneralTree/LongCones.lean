import Milliken.GeneralTree.BoundaryIndex
import Milliken.GeneralTree.Ancestry

/-!
# Nonempty long successor cones at arbitrary selected levels

Let B be an infinite strong subtree of an arbitrary pruned locally
finitely branching rooted ambient tree U. For any B-selected node x,
any ambient immediate child y of x, and any later B-selected level,
there is a retained descendant of y on that later level.

Consequently we may select a representative of every ambient child
cone at the same later selected level, even if the number of children
depends on x and becomes arbitrarily large elsewhere in U.
Representatives from distinct immediate-child cones are distinct.

This is a building block for thinning a B-tree to a chosen infinite
subsequence of its selected levels, needed for the protected A.3(2)
splice outside the distinguished finite-stem cones.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Each selected source level beyond a retained node contains
a descendant of that node. -/
theorem exists_sourceLevel_descendant
    (B : StrongSubtree U)
    {m ell : ℕ} (hme : m ≤ ell)
    {x : U} (hx : x ∈ B.sourceLevel m) :
    ∃ z : U, z ∈ B.sourceLevel ell ∧ x ≤ z := by
  induction ell, hme using Nat.le_induction with
  | base =>
      exact ⟨x, hx, le_rfl⟩
  | succ ell hme ih =>
      obtain ⟨z, hz, hxz⟩ := ih
      obtain ⟨y, hzy⟩ := U.has_child z
      obtain ⟨w, hw, _⟩ :=
        B.successor_unique ell z hz.1 hz.2 y hzy
      exact ⟨w, ⟨hw.1, hw.2.1⟩,
        hxz.trans (hzy.le.trans hw.2.2)⟩

/-- Every immediate ambient child cone of a retained node
meets each strictly later selected source level. -/
theorem exists_sourceLevel_descendant_in_childCone
    (B : StrongSubtree U)
    {m ell : ℕ} (hme : m < ell)
    {x y : U} (hx : x ∈ B.sourceLevel m)
    (hxy : x ⋖ y) :
    ∃ z : U, z ∈ B.sourceLevel ell ∧ y ≤ z := by
  obtain ⟨z, hz, _⟩ :=
    B.successor_unique m x hx.1 hx.2 y hxy
  have hm1 : m + 1 ≤ ell := by omega
  obtain ⟨w, hw, hzw⟩ :=
    B.exists_sourceLevel_descendant hm1
      (show z ∈ B.sourceLevel (m + 1) from
        ⟨hz.1, hz.2.1⟩)
  exact ⟨w, hw, hz.2.2.trans hzw⟩

/-- A canonical (classically chosen) later selected node in
the cone of a given immediate child of x. -/
noncomputable def longConeRepresentative
    (B : StrongSubtree U)
    {m ell : ℕ} (hme : m < ell)
    {x : U} (hx : x ∈ B.sourceLevel m)
    (y : ChildIndex U x) : U :=
  Classical.choose
    (B.exists_sourceLevel_descendant_in_childCone
      hme hx y.2)

/-- The chosen representative is at the requested source level
and lies above the specified child. -/
theorem longConeRepresentative_spec
    (B : StrongSubtree U)
    {m ell : ℕ} (hme : m < ell)
    {x : U} (hx : x ∈ B.sourceLevel m)
    (y : ChildIndex U x) :
    B.longConeRepresentative hme hx y ∈ B.sourceLevel ell ∧
      (y : U) ≤ B.longConeRepresentative hme hx y :=
  Classical.choose_spec
    (B.exists_sourceLevel_descendant_in_childCone
      hme hx y.2)

/-- Two different ambient immediate successors of x have no
common descendant: comparability of predecessors and their
equal ambient rank force equality. -/
theorem immediateChildren_eq_of_common_descendant
    (U : AmbientTree) {x y z w : U}
    (hxy : x ⋖ y) (hxz : x ⋖ z)
    (hyw : y ≤ w) (hzw : z ≤ w) : y = z := by
  have heq : U.level y = U.level z := by
    calc
      U.level y = U.level x + 1 := U.level_covBy hxy
      _ = U.level z := (U.level_covBy hxz).symm
  rcases le_total_of_directed hyw hzw with hzy | hyz
  · exact (U.eq_of_le_of_level_eq hzy heq.symm).symm
  · exact U.eq_of_le_of_level_eq hyz heq

/-- Representatives of distinct immediate-child cones are
distinct even when the local branching degree is unbounded. -/
theorem longConeRepresentative_injective
    (B : StrongSubtree U)
    {m ell : ℕ} (hme : m < ell)
    {x : U} (hx : x ∈ B.sourceLevel m) :
    Function.Injective (B.longConeRepresentative hme hx) := by
  intro y z h
  apply Subtype.ext
  have hy := (B.longConeRepresentative_spec hme hx y).2
  have hz := (B.longConeRepresentative_spec hme hx z).2
  have hy' :
      (y : U) ≤ B.longConeRepresentative hme hx z := by
    simpa only [h] using hy
  have hchild :
      (y : U) = (z : U) :=
    immediateChildren_eq_of_common_descendant U y.2 z.2
      hy' hz
  exact hchild

end StrongSubtree
end GeneralTree
end Milliken
