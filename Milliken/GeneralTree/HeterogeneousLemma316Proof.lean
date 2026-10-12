import Milliken.GeneralTree.HeterogeneousLemma316Tower
import Milliken.GeneralTree.HeterogeneousSparseFiniteHL
import Milliken.GeneralTree.HeterogeneousFillOutside

/-!
# The heterogeneous form of Todorčević's Lemma 3.16

This is the sparse finite Halpern--Läuchli argument after the
bounded-witness Lemma 3.16 tower, now carried out in arbitrary
pruned, locally finitely branching strong-tree products.

A sparse complementary matrix is filled outside its base cones,
becomes globally level-dense, and contradicts the tower's
uniformly good sections. Thus the desired dense section survives.
All source heights refer to selected source indices of the
actual, potentially non-isomorphic factors; no common fixed
branching alphabet or uniform bound is assumed.

The only higher-dimensional combinatorial input is the explicitly
passed HDHL theorem in the *front* dimension d. No unproved
Halpern--Läuchli axiom is introduced.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The heterogeneous Lemma 3.16. Under the stabilization
and complement-density reductions, every last-coordinate cone
contains a section with a common-support front matrix dense at
any prescribed source index k and lying in the original Q-section.
The source support of this matrix is strictly above the selected
source index of the last-coordinate node. -/
theorem heterogeneousLemma316
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL
      (fun i : Fin d => P i.castSucc))
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r) :
    ∃ y : U, ∃ M : HeterogeneousMatrix
        (fun i : Fin d => P i.castSucc),
      ∃ l : ℕ,
        t ≤ y ∧
        (∃ q : ℕ,
          y ∈ (P (Fin.last d)).sourceLevel q ∧ q < l) ∧
        M.OnLevel l ∧ M.DenseAt k ∧
        M.carrier ⊆ heterogeneousLastSection Q y := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  let Tower : ℕ →
      HeterogeneousLemma316TowerState (P (Fin.last d)) :=
    heterogeneousLemma316Tower P Q hd hstab hno k r t ht
  let levels : ℕ → ℕ := fun p => (Tower p).n
  have hlevels : StrictMono levels :=
    heterogeneousLemma316Tower_levels_strictMono
      P Q hd hstab hno k r t ht
  have hunbounded : ∀ b : ℕ, ∃ p : ℕ, b ≤ levels p :=
    heterogeneousLemma316Tower_levels_unbounded
      P Q hd hstab hno k r t ht
  have hk0 : 0 < levels 0 := by
    dsimp [levels, Tower, heterogeneousLemma316Tower,
      initialHeterogeneousLemma316TowerState]
    omega
  have hk_le_zero : k ≤ levels 0 := by
    dsimp [levels, Tower, heterogeneousLemma316Tower,
      initialHeterogeneousLemma316TowerState]
    exact Nat.le_max_left _ _
  obtain ⟨L, hfinite⟩ :=
    heterogeneousSparseFiniteHL_of_hdhl
      Front hHDHL hk0 hlevels hunbounded
  obtain ⟨p, hLp⟩ := hunbounded L
  let Full : HeterogeneousMatrix Front :=
    HeterogeneousMatrix.fullLevel Front (levels p)
  have hFullDense : Full.DenseAt (levels p) :=
    HeterogeneousMatrix.fullLevel_denseAt Front (levels p)
  have hFullL : Full.DenseAt L :=
    Full.denseAt_of_le hLp hFullDense
  let S : HeterogeneousLemma316TowerState
      (P (Fin.last d)) := Tower p
  let y : U := S.sample
  have hyX : y ∈ S.X := S.sample_mem
  have hybelow : S.sampleIndex < levels p := S.sample_below
  have hySource :
      y ∈ (P (Fin.last d)).sourceLevel S.sampleIndex :=
    S.sample_source
  have hyt : t ≤ y := by
    have hsub :=
      heterogeneousLemma316Tower_X_antitone
        P Q hd hstab hno k r t ht
        (p := 0) (q := p) (Nat.zero_le p)
    have hyX0 :
        y ∈ (Tower 0).X := hsub hyX
    change y ∈ {z : U |
      z ∈ (P (Fin.last d)).carrier ∧ t ≤ z} at hyX0
    exact hyX0.2
  let K0 : Set (Fin d → U) :=
    heterogeneousLastSection (heterogeneousTailNormalize P Q) y
  rcases hfinite Full hFullL K0 with hone | hzero
  · obtain ⟨N, hNsparse, hNsub⟩ := hone
    obtain ⟨q, base, hNdense⟩ := hNsparse
    have hqnext : levels q ≤ levels (q + 1) :=
      (hlevels (Nat.lt_succ_self q)).le
    have hNnonempty : ∀ i, (N.coord i).Nonempty := by
      intro i
      obtain ⟨z, hz, hbasez⟩ :=
        (Front i).exists_sourceLevel_descendant
          hqnext (base.2 i)
      obtain ⟨w, hw, _⟩ :=
        hNdense i z hz hbasez
      exact ⟨w, hw⟩
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel (levels p) :=
      N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
        (HeterogeneousMatrix.fullLevel_onLevel
          Front (levels p)) hNnonempty
    have hnextLe : levels (q + 1) ≤ levels p :=
      heterogeneous_support_ge_of_onLevel_denseAbove
        Front hd base hqnext N hNlevel hNdense
    have hIndex : q + 1 ≤ p := by
      by_contra hnot
      have hpq : p < q + 1 := Nat.lt_of_not_ge hnot
      have hlt := hlevels hpq
      omega
    have hyNext :
        y ∈ (Tower (q + 1)).X := by
      have hsub :=
        heterogeneousLemma316Tower_X_antitone
          P Q hd hstab hno k r t ht hIndex
      exact hsub hyX
    let A : HeterogeneousMatrix Front :=
      N.fillOutsideAbove base.1 (levels p)
    have hAlevel : A.LevelDenseAt (levels (q + 1)) := by
      exact N.fillOutsideAbove_levelDenseAt_of_later
        base hqnext hnextLe hNlevel hNdense
    have hgood :
        HeterogeneousSectionsGoodAt
          P (heterogeneousTailNormalize P Q)
          (levels q) (levels (q + 1))
          (Tower (q + 1)).X :=
      heterogeneousLemma316Tower_good
        P Q hd hstab hno k r t ht q
    have hprod :
        HeterogeneousProductDenseAt Front
          (heterogeneousLastSection
            (heterogeneousTailNormalize P Q) y ∩ A.carrier)
          (levels q) :=
      hgood y hyNext A hAlevel
    obtain ⟨z, hz, hbasez⟩ := hprod base
    have hzN : z ∈ N.carrier :=
      N.mem_carrier_of_fillOutsideAbove_of_above
        base.1 (levels p) hz.2 hbasez
    have hzCompl : z ∈ K0ᶜ := (hNsub hzN).2
    have hzK0 : z ∈ K0 := hz.1
    exact False.elim (hzCompl hzK0)
  · obtain ⟨N, hNdense0, hNsub⟩ := hzero
    have hNnonempty : ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAt hNdense0
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel (levels p) :=
      N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
        (HeterogeneousMatrix.fullLevel_onLevel
          Front (levels p)) hNnonempty
    have hNdense : N.DenseAt k :=
      N.denseAt_of_le hk_le_zero hNdense0
    have hNsubQ :
        N.carrier ⊆ heterogeneousLastSection Q y := by
      intro z hzN
      have hzK0 : z ∈ K0 := (hNsub hzN).2
      let zv : HeterogeneousLevelTuple Front (levels p) :=
        ⟨z, fun i => hNlevel i (z i) (hzN i)⟩
      exact (heterogeneousTailNormalize_section_of_above
        P Q hd y hySource zv hybelow).mp hzK0
    exact ⟨y, N, levels p, hyt,
      ⟨S.sampleIndex, hySource, hybelow⟩,
      hNlevel, hNdense, hNsubQ⟩

end GeneralTree
end Milliken
