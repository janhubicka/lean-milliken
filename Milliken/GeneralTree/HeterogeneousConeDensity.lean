import Milliken.GeneralTree.HeterogeneousHDHLBase

/-!
# Local cone-density operations for heterogeneous Halpern--Läuchli

These are the arbitrary locally finitely branching versions of the
`restrictAbove` and `fillOutsideAbove` operations used in
Todorčević's Section 3.2 asymmetric density argument.

For a coordinate tuple `base`, `DenseAbove base n` means that every
node of the n-th selected source level in the descendant cone of
`base i` extends to a node in the i-th matrix coordinate. The
complementary fill keeps all matrix nodes and adds the nodes of
the n-th source level *outside* the chosen cones. This turns cone
density into global density without introducing a uniform degree bound.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}
variable {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- Coordinatewise density in the descendant cones of a base tuple,
at an arbitrary selected source height. -/
def DenseAbove (M : HeterogeneousMatrix P)
    (base : Fin d → U) (n : ℕ) : Prop :=
  ∀ i : Fin d, ∀ x ∈ (P i).sourceLevel n,
    base i ≤ x → ∃ y, y ∈ M.coord i ∧ x ≤ y

/-- Retain only those matrix nodes above the given base tuple. -/
def restrictAbove (M : HeterogeneousMatrix P)
    (base : Fin d → U) : HeterogeneousMatrix P where
  coord := fun i => {x | x ∈ M.coord i ∧ base i ≤ x}
  coord_sub := by
    intro i x hx
    exact M.coord_sub i hx.1

/-- Restricting a globally n-dense matrix above a base tuple
gives n-density above precisely that base. -/
theorem restrictAbove_denseAbove
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) (n : ℕ)
    (hM : M.DenseAt n) :
    (M.restrictAbove base).DenseAbove base n := by
  intro i x hx hbase
  obtain ⟨y, hy, hxy⟩ := hM i x hx
  exact ⟨y, ⟨hy, hbase.trans hxy⟩, hxy⟩

/-- Restricting above a base preserves the matrix's carrier inclusion. -/
theorem restrictAbove_carrier_subset
    (M : HeterogeneousMatrix P) (base : Fin d → U) :
    (M.restrictAbove base).carrier ⊆ M.carrier := by
  intro x hx i
  exact (hx i).1

/-- Complete a cone-dense matrix to a globally dense one:
inside the chosen base cone use M; outside it, take the entire
selected source level of the input factor. -/
def fillOutsideAbove (M : HeterogeneousMatrix P)
    (base : Fin d → U) (n : ℕ) : HeterogeneousMatrix P where
  coord := fun i =>
    M.coord i ∪
      {x | x ∈ (P i).sourceLevel n ∧ ¬ base i ≤ x}
  coord_sub := by
    intro i x hx
    rcases hx with hm | hout
    · exact M.coord_sub i hm
    · exact hout.1.1

/-- Density above the selected base cones suffices to make the
completed matrix globally dense on the same selected level. -/
theorem fillOutsideAbove_denseAt
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) (n : ℕ)
    (hM : M.DenseAbove base n) :
    (M.fillOutsideAbove base n).DenseAt n := by
  intro i x hx
  by_cases hinside : base i ≤ x
  · obtain ⟨y, hy, hxy⟩ := hM i x hx hinside
    exact ⟨y, Or.inl hy, hxy⟩
  · exact ⟨x, Or.inr ⟨hx, hinside⟩, le_rfl⟩

/-- If a product tuple from the completed matrix lies above
the selected base in every coordinate, it already belongs
to the original cone-dense matrix. -/
theorem mem_carrier_of_fillOutsideAbove_of_above
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) (n : ℕ)
    {x : Fin d → U}
    (hx : x ∈ (M.fillOutsideAbove base n).carrier)
    (hbase : ∀ i, base i ≤ x i) :
    x ∈ M.carrier := by
  intro i
  rcases hx i with hM | hout
  · exact hM
  · exact (hout.2 (hbase i)).elim

/-- Cone-density at a later selected source index implies cone-density
at every earlier index. Extend each test node to the later level,
remaining in the same cone above its base. -/
theorem denseAbove_of_le
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {m n : ℕ}
    (hmn : m ≤ n) (hM : M.DenseAbove base n) :
    M.DenseAbove base m := by
  intro i x hx hbase
  obtain ⟨z, hz, hxz⟩ :=
    (P i).exists_sourceLevel_descendant hmn hx
  obtain ⟨y, hy, hzy⟩ :=
    hM i z hz (hbase.trans hxz)
  exact ⟨y, hy, hxz.trans hzy⟩

end HeterogeneousMatrix

/-- Product density is downward closed in its selected source index.
Extending each input coordinate from source level m to source level n
uses only the source tree's strongness and unbounded local finiteness. -/
theorem heterogeneousProductDenseAt_of_le
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U))
    {m n : ℕ} (hmn : m ≤ n)
    (hQ : HeterogeneousProductDenseAt P Q n) :
    HeterogeneousProductDenseAt P Q m := by
  classical
  intro x
  let y : Fin d → U :=
    fun i => Classical.choose
      ((P i).exists_sourceLevel_descendant hmn (x.2 i))
  have hy : ∀ i, y i ∈ (P i).sourceLevel n := by
    intro i
    exact (Classical.choose_spec
      ((P i).exists_sourceLevel_descendant hmn (x.2 i))).1
  have hxy : ∀ i, x.1 i ≤ y i := by
    intro i
    exact (Classical.choose_spec
      ((P i).exists_sourceLevel_descendant hmn (x.2 i))).2
  obtain ⟨z, hz, hyz⟩ := hQ ⟨y, hy⟩
  exact ⟨z, hz, fun i => (hxy i).trans (hyz i)⟩

end GeneralTree
end Milliken
