import Milliken.GeneralTree.HeterogeneousAtScaleAvoid
import Milliken.GeneralTree.HeterogeneousSomewhereDense
import Milliken.GeneralTree.HeterogeneousBadSectionDensity

/-!
# The heterogeneous form of Todorčević's Lemma 3.15

This closes the contradiction argument after explicit tail
normalization, with genuinely heterogeneous locally finitely
branching strong trees. The initial last-coordinate cone is kept
fixed. At one chosen common source index n, its finite selected
frontier is processed by the arbitrary-scale avoidance recursion.
The resulting front matrix and finite set of last-coordinate witnesses
form a somewhere-dense matrix in the complement of normalized Q.

The normalization is only used to preserve old avoided sections;
since Q is contained in its normalization, absence of
somewhere-dense matrices in Qᶜ suffices to contradict the constructed
complementary matrix. This is the analogue of the proved homogeneous
\`lemma315_tailNormalize\`, not an assumed Halpern--Läuchli theorem.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

namespace HeterogeneousMatrix

/-- Appending a coordinate that is source-n-dense above its chosen
last-tree root preserves cone density of the whole product. -/
theorem snoc_denseAbove
    (P : Fin (d + 1) → StrongSubtree U)
    (M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hY : Y ⊆ (P (Fin.last d)).carrier)
    (base : Fin d → U)
    (t : U)
    (n : ℕ)
    (hM : M.DenseAbove base n)
    (hYdense : ∀ z ∈ (P (Fin.last d)).sourceLevel n,
      t ≤ z → ∃ y, y ∈ Y ∧ z ≤ y) :
    (M.snoc P Y hY).DenseAbove
      (heteroAppendLast base t) n := by
  intro i z hz hbase
  cases i using Fin.lastCases with
  | last =>
      have htz : t ≤ z := by
        simpa [heteroAppendLast] using hbase
      simpa [HeterogeneousMatrix.snoc] using
        hYdense z hz htz
  | cast j =>
      have hbz : base j ≤ z := by
        simpa [heteroAppendLast] using hbase
      simpa [HeterogeneousMatrix.snoc] using
        hM j z hz hbz

end HeterogeneousMatrix

/-- Heterogeneous version of Todorčević's Lemma 3.15 for the
corrected tail-normalized set. A cone-dense family of
last-coordinate nodes has a cone-dense subfamily on which
all sections are uniformly good at one front-density scale.

All trees have only locally finite branching, and the coordinate
strong subtrees may be non-isomorphic with different source levels. -/
theorem heterogeneousLemma315_tailNormalize
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k : ℕ) (X : Set U)
    (hXinside : X ⊆ (P (Fin.last d)).carrier)
    (hXsome : HeterogeneousSomewhereConeDense
      (P (Fin.last d)) X) :
    ∃ n : ℕ, ∃ Y : Set U,
      Y ⊆ X ∧
      HeterogeneousSomewhereConeDense
        (P (Fin.last d)) Y ∧
      HeterogeneousSectionsGoodAt
        P (heterogeneousTailNormalize P Q) k n Y := by
  classical
  by_contra hfail
  have hnoN :
      ¬ HeterogeneousContainsSomewhereDense
        P (heterogeneousTailNormalize P Q)ᶜ := by
    rintro ⟨M, hSome, hSub⟩
    exact hno ⟨M, hSome,
      hSub.trans (heterogeneousTailNormalize_compl_subset P Q)⟩
  obtain ⟨C, hmin⟩ :=
    exists_minimalHeterogeneousAvoidCover
      P (heterogeneousTailNormalize P Q) k
      hXinside hXsome
  obtain ⟨base, hxD⟩ :=
    heterogeneousMinimalAvoidCover_nonempty
      P (heterogeneousTailNormalize P Q) k X hfail C
  let T : StrongSubtree U := P (Fin.last d)
  obtain ⟨r, hr⟩ :=
    T.carrier_levels C.root C.root_mem
  let n : ℕ := max k r + 1
  have hkn : k < n := by
    dsimp [n]
    omega
  have hrn : r < n := by
    dsimp [n]
    omega
  let E : Finset U :=
    ((T.sourceLevel_finite n).toFinset).filter
      (fun z => C.root ≤ z)
  have hE (z : U) :
      z ∈ E ↔ z ∈ T.sourceLevel n ∧ C.root ≤ z := by
    simp [E]
  have hEinside :
      ∀ z ∈ E, z ∈ T.carrier ∧ C.root ≤ z := by
    intro z hz
    obtain ⟨hzLevel, hrootz⟩ := (hE z).mp hz
    exact ⟨hzLevel.1, hrootz⟩
  obtain ⟨S⟩ :=
    exists_heterogeneousAtScaleAvoidState
      P Q hd hstab base C hmin hxD
      n hkn E hEinside
  have hYinside : (S.Y : Set U) ⊆ T.carrier := by
    intro y hy
    obtain ⟨q, hSource, _⟩ := S.belowSupport y hy
    exact hSource.1
  have hYdense :
      ∀ z ∈ T.sourceLevel n, C.root ≤ z →
        ∃ y, y ∈ (S.Y : Set U) ∧ z ≤ y := by
    intro z hz hrootz
    obtain ⟨y, hyY, hzy⟩ :=
      S.covers z ((hE z).mpr ⟨hz, hrootz⟩)
    exact ⟨y, hyY, hzy⟩
  let M : HeterogeneousMatrix P :=
    S.M.snoc P (S.Y : Set U) hYinside
  have hMdense :
      M.DenseAbove (heteroAppendLast base.1 C.root) n := by
    exact HeterogeneousMatrix.snoc_denseAbove
      P S.M (S.Y : Set U) hYinside
      base.1 C.root n S.dense hYdense
  have hbase :
      ∀ i : Fin (d + 1), ∃ j : ℕ, j < n ∧
        heteroAppendLast base.1 C.root i ∈
          (P i).sourceLevel j := by
    intro i
    cases i using Fin.lastCases with
    | last =>
        refine ⟨r, hrn, ?_⟩
        simpa [T] using
          (show C.root ∈ T.sourceLevel r from
            ⟨C.root_mem, hr⟩)
    | cast j =>
        refine ⟨k, hkn, ?_⟩
        simpa using base.2 j
  have hSome : M.SomewhereDense :=
    ⟨heteroAppendLast base.1 C.root, n, hbase, hMdense⟩
  have hMsub :
      M.carrier ⊆ (heterogeneousTailNormalize P Q)ᶜ :=
    heterogeneousSnoc_carrier_subset_compl
      P S.M (S.Y : Set U) hYinside
      (heterogeneousTailNormalize P Q) S.avoids
  exact hnoN ⟨M, hSome, hMsub⟩

end GeneralTree
end Milliken
