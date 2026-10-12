import Milliken.GeneralTree.HeterogeneousSparseWitness
import Milliken.GeneralTree.HeterogeneousLevelSupport

/-!
# Transporting finite heterogeneous HL certificates into dense matrices

Given a matrix M dense at source index l and a finite certificate W
whose coordinates have source index at most l, map each node of W
to an M-node extending it. A total transport is defined by using an
arbitrary M-point outside the domain where extension is possible.

The product image preserves the finite witness's global density or
its sparse cone density. The construction uses actual strong-tree
source indices and works with unrelated, unbounded node degrees.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ} {P : Fin d → StrongSubtree U}

namespace StrongSubtree

/-- Source index of a retained node, with an irrelevant default
value outside the carrier. -/
noncomputable def sourceIndex (S : StrongSubtree U) (x : U) : ℕ := by
  classical
  exact if h : x ∈ S.carrier then
    Classical.choose (S.carrier_levels x h)
  else 0

theorem mem_sourceLevel_sourceIndex
    (S : StrongSubtree U) {x : U}
    (hx : x ∈ S.carrier) :
    x ∈ S.sourceLevel (S.sourceIndex x) := by
  refine ⟨hx, ?_⟩
  simp only [sourceIndex, dif_pos hx]
  exact Classical.choose_spec (S.carrier_levels x hx)

end StrongSubtree

namespace HeterogeneousSparseFiniteHLWitness

variable {k : ℕ} {levels : ℕ → ℕ}

/-- Maximum source index appearing in the finite i-th coordinate
of a sparse witness. -/
noncomputable def coordSourceBound
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (i : Fin d) : ℕ := by
  classical
  exact (W.coordFinite i).toFinset.sup
    (fun x => (P i).sourceIndex x)

/-- One natural source index bounding all coordinates of a
finite sparse witness, even for non-isomorphic factor trees. -/
noncomputable def sourceBound
    (W : HeterogeneousSparseFiniteHLWitness P k levels) : ℕ := by
  classical
  exact Finset.univ.sup W.coordSourceBound

theorem sourceIndex_le_sourceBound
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    {i : Fin d} {x : U}
    (hx : x ∈ W.M.coord i) :
    (P i).sourceIndex x ≤ W.sourceBound := by
  classical
  have hcoord : (P i).sourceIndex x ≤ W.coordSourceBound i := by
    unfold coordSourceBound
    exact Finset.le_sup
      (f := fun x : U => (P i).sourceIndex x)
      (by simpa using hx)
  exact hcoord.trans
    (Finset.le_sup (f := W.coordSourceBound) (Finset.mem_univ i))

end HeterogeneousSparseFiniteHLWitness

namespace HeterogeneousMatrix

/-- Given a globally l-dense matrix, map every U-node into the
i-th coordinate of M. If an M-extension exists choose it,
otherwise take a fixed M-point. -/
noncomputable def extendIntoDense
    (M : HeterogeneousMatrix P) {l : ℕ}
    (hM : M.DenseAt l)
    (i : Fin d) (x : U) : U := by
  classical
  exact if h : ∃ y : U, y ∈ M.coord i ∧ x ≤ y then
    Classical.choose h
  else
    Classical.choose (M.coord_nonempty_of_denseAt hM i)

theorem extendIntoDense_mem
    (M : HeterogeneousMatrix P) {l : ℕ}
    (hM : M.DenseAt l)
    (i : Fin d) (x : U) :
    M.extendIntoDense hM i x ∈ M.coord i := by
  classical
  unfold extendIntoDense
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · exact Classical.choose_spec (M.coord_nonempty_of_denseAt hM i)

/-- On every retained node at a source index no later than l,
the total map actually chooses a descendant. -/
theorem le_extendIntoDense
    (M : HeterogeneousMatrix P) {l j : ℕ}
    (hM : M.DenseAt l)
    (i : Fin d) {x : U}
    (hx : x ∈ (P i).sourceLevel j)
    (hjl : j ≤ l) :
    x ≤ M.extendIntoDense hM i x := by
  classical
  obtain ⟨z, hz, hxz⟩ :=
    (P i).exists_sourceLevel_descendant hjl hx
  obtain ⟨y, hy, hzy⟩ := hM i z hz
  have hex : ∃ y : U, y ∈ M.coord i ∧ x ≤ y :=
    ⟨y, hy, hxz.trans hzy⟩
  simp only [extendIntoDense, dif_pos hex]
  exact (Classical.choose_spec hex).2

end HeterogeneousMatrix

namespace HeterogeneousSparseFiniteHLWitness

variable {k l : ℕ} {levels : ℕ → ℕ}

/-- Coordinatewise image of a sparse finite witness, placed inside
an arbitrary source-l-dense heterogeneous product matrix. -/
noncomputable def transport
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (M : HeterogeneousMatrix P) (hM : M.DenseAt l) :
    HeterogeneousMatrix P where
  coord := fun i =>
    (M.extendIntoDense hM i) '' W.M.coord i
  coord_sub := by
    intro i z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact M.coord_sub i (M.extendIntoDense_mem hM i x)

theorem transport_carrier_subset
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (M : HeterogeneousMatrix P) (hM : M.DenseAt l) :
    (W.transport M hM).carrier ⊆ M.carrier := by
  intro x hx i
  obtain ⟨s, hs, hxs⟩ := hx i
  rw [← hxs]
  exact M.extendIntoDense_mem hM i s

/-- Decode a point of the transported product as the coordinatewise
image of a point of the original finite witness. -/
theorem exists_source_of_transport
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (M : HeterogeneousMatrix P) (hM : M.DenseAt l)
    {z : Fin d → U} (hz : z ∈ (W.transport M hM).carrier) :
    ∃ x ∈ W.M.carrier,
      ∀ i, M.extendIntoDense hM i (x i) = z i := by
  classical
  choose x hxW hx using fun i => hz i
  exact ⟨x, (fun i => hxW i), hx⟩

/-- The transport preserves original global density whenever its
target source index l bounds all source indices in W. -/
theorem transport_denseAt
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (M : HeterogeneousMatrix P) (hM : M.DenseAt l)
    (hbound : W.sourceBound ≤ l)
    (hW : W.M.DenseAt k) :
    (W.transport M hM).DenseAt k := by
  intro i x hx
  obtain ⟨y, hyW, hxy⟩ := hW i x hx
  refine ⟨M.extendIntoDense hM i y, ?_, ?_⟩
  · exact ⟨y, hyW, rfl⟩
  · have hySource :
        y ∈ (P i).sourceLevel ((P i).sourceIndex y) :=
      (P i).mem_sourceLevel_sourceIndex (W.M.coord_sub i hyW)
    exact hxy.trans
      (M.le_extendIntoDense hM i hySource
        ((W.sourceIndex_le_sourceBound hyW).trans hbound))

/-- The same transport preserves sparse somewhere density, including
the source-level base vector and adjacent density scale. -/
theorem transport_sparse
    (W : HeterogeneousSparseFiniteHLWitness P k levels)
    (M : HeterogeneousMatrix P) (hM : M.DenseAt l)
    (hbound : W.sourceBound ≤ l)
    (hW : HeterogeneousSparseSomewhereDense P levels W.M) :
    HeterogeneousSparseSomewhereDense P levels
      (W.transport M hM) := by
  obtain ⟨q, base, hDense⟩ := hW
  refine ⟨q, base, ?_⟩
  intro i x hx hbase
  obtain ⟨y, hyW, hxy⟩ := hDense i x hx hbase
  refine ⟨M.extendIntoDense hM i y, ?_, ?_⟩
  · exact ⟨y, hyW, rfl⟩
  · have hySource :
        y ∈ (P i).sourceLevel ((P i).sourceIndex y) :=
      (P i).mem_sourceLevel_sourceIndex (W.M.coord_sub i hyW)
    exact hxy.trans
      (M.le_extendIntoDense hM i hySource
        ((W.sourceIndex_le_sourceBound hyW).trans hbound))

end HeterogeneousSparseFiniteHLWitness
end GeneralTree
end Milliken
