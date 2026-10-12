import Milliken.GeneralTree.HeterogeneousSparseTransport

/-!
# Uniform finite sparse Halpern--Läuchli for heterogeneous trees

This is the sparse finite-product consequence of *same-dimensional*
heterogeneous HDHL. The proof follows Todorčević §3.2:
finite monochromatic certificates form an open cover of binary
colouring space; compactness produces finitely many certificates;
the largest source index appearing in them gives one uniform input
density bound; then each certificate is transported into an arbitrary
dense product matrix.

Neither the factor trees nor their branching degrees are assumed
isomorphic or uniformly bounded. No new HL axiom is introduced.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A uniform finite two-colour dichotomy for any source-l-dense
matrix: either colour 0 contains a globally source-k-dense matrix,
or colour 1 contains a matrix dense inside some cones between two
adjacent prescribed source indices.

The only non-elementary input is the explicitly stated
\`HasHeterogeneousHDHL P\` hypothesis in the same dimension; this
hypothesis is not yet proved in all dimensions. -/
theorem heterogeneousSparseFiniteHL_of_hdhl
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    {k : ℕ} (hk : 0 < k)
    {levels : ℕ → ℕ}
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    ∃ l : ℕ, ∀ M : HeterogeneousMatrix P,
      M.DenseAt l →
      ∀ K0 : Set (Fin d → U),
        (∃ M1 : HeterogeneousMatrix P,
          HeterogeneousSparseSomewhereDense P levels M1 ∧
          M1.carrier ⊆ M.carrier ∩ K0ᶜ) ∨
        (∃ M0 : HeterogeneousMatrix P,
          M0.DenseAt k ∧
          M0.carrier ⊆ M.carrier ∩ K0) := by
  classical
  obtain ⟨F, hcover⟩ :=
    exists_heterogeneousSparseFiniteHLWitness_subcover
      P hHDHL hk hlevels hunbounded
  let L : ℕ := F.sup
    (fun W : HeterogeneousSparseFiniteHLWitness P k levels =>
      W.sourceBound)
  let l : ℕ := max k L
  refine ⟨l, ?_⟩
  intro M hM K0
  let mapTuple : (Fin d → U) → (Fin d → U) :=
    fun x i => M.extendIntoDense hM i (x i)
  let c : (Fin d → U) → Fin 2 :=
    fun x => if mapTuple x ∈ K0 then 0 else 1
  have hc :
      c ∈ ⋃ W ∈ F, W.cylinder :=
    hcover (Set.mem_univ c)
  simp only [Set.mem_iUnion] at hc
  obtain ⟨W, hWF, hcW⟩ := hc
  have hbound : W.sourceBound ≤ l := by
    have hL : W.sourceBound ≤ L :=
      Finset.le_sup
        (f := fun W : HeterogeneousSparseFiniteHLWitness P k levels =>
          W.sourceBound) hWF
    exact hL.trans (Nat.le_max_right k L)
  let N : HeterogeneousMatrix P := W.transport M hM
  have hNsubM : N.carrier ⊆ M.carrier :=
    W.transport_carrier_subset M hM
  rcases W.shape with hzero | hone
  · right
    obtain ⟨hcolor, hWdense⟩ := hzero
    have hNdense : N.DenseAt k :=
      W.transport_denseAt M hM hbound hWdense
    refine ⟨N, hNdense, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    obtain ⟨x, hxW, hxmap⟩ :=
      W.exists_source_of_transport M hM hz
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 0 :=
      (hcW x hxW).trans hcolor
    by_contra hzNotK
    have hcx1 : c x = 1 := by
      simp [c, hmap, hzNotK]
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcx.symm.trans hcx1)
  · left
    obtain ⟨hcolor, hWsparse⟩ := hone
    have hNsparse : HeterogeneousSparseSomewhereDense P levels N :=
      W.transport_sparse M hM hbound hWsparse
    refine ⟨N, hNsparse, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    intro hzK
    obtain ⟨x, hxW, hxmap⟩ :=
      W.exists_source_of_transport M hM hz
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 1 :=
      (hcW x hxW).trans hcolor
    have hcx0 : c x = 0 := by
      simp [c, hmap, hzK]
    exact (by decide : (1 : Fin 2) ≠ 0)
      (hcx.symm.trans hcx0)

end GeneralTree
end Milliken
