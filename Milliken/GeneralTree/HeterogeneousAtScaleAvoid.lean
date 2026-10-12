import Milliken.GeneralTree.HeterogeneousNormalizedAvoidState

/-!
# Arbitrary source-scale finite avoidance recursion

This is the form of the finite recursion actually needed in the
contradiction of heterogeneous Lemma 3.15: a *fixed* front source-k
tuple and an arbitrarily large target source index n. The last
coordinate witnesses are chosen above an arbitrary finite family
of retained last-tree nodes descending from the minimum cover root.

The recursion neither enumerates a globally fixed alphabet nor
bounds the finite local branching degree. It retains density at n,
even as the level support increases with each new avoided section.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- A level-supported, cone-dense front matrix avoiding all sections
indexed by Y, and with Y covering every processed last-coordinate
node in E. The target density index n is independent of any last
coordinate's source index. -/
structure HeterogeneousAtScaleAvoidState
    {d k : ℕ}
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (n : ℕ) (E : Finset U) where
  M : HeterogeneousMatrix (fun i : Fin d => P i.castSucc)
  level : ℕ
  Y : Finset U
  onLevel : M.OnLevel level
  dense : M.DenseAbove base.1 n
  aboveBase : ∀ z ∈ M.carrier, ∀ i, base.1 i ≤ z i
  avoids : ∀ y ∈ Y,
    M.carrier ⊆
      (heterogeneousLastSection (heterogeneousTailNormalize P Q) y)ᶜ
  belowSupport : ∀ y ∈ Y,
    ∃ q : ℕ, y ∈ (P (Fin.last d)).sourceLevel q ∧ q < level
  covers : ∀ v ∈ E, ∃ y ∈ Y, v ≤ y
  baseBelowSupport : k < level

/-- Full source level n restricted to the base cones initializes
the construction whenever the target source index exceeds k. -/
noncomputable def initialHeterogeneousAtScaleAvoidState
    {d k n : ℕ}
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (hkn : k < n) :
    HeterogeneousAtScaleAvoidState P Q base n ∅ := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  let F : HeterogeneousMatrix Front :=
    HeterogeneousMatrix.fullLevel Front n
  let M : HeterogeneousMatrix Front := F.restrictAbove base.1
  exact {
    M := M
    level := n
    Y := ∅
    onLevel := by
      intro i z hz
      exact hz.1
    dense := by
      intro i z hz hbase
      exact ⟨z, ⟨hz, hbase⟩, le_rfl⟩
    aboveBase := by
      intro z hz i
      exact (hz i).2
    avoids := by
      intro y hy
      simp at hy
    belowSupport := by
      intro y hy
      simp at hy
    covers := by
      intro v hv
      simp at hv
    baseBelowSupport := hkn
  }

/-- Simultaneous avoidance of any finite collection of last-coordinate
nodes, while retaining a fixed prescribed source-index density n. -/
theorem exists_heterogeneousAtScaleAvoidState
    {d k : ℕ}
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    {X : Set U}
    (C : HeterogeneousAvoidCover P
      (heterogeneousTailNormalize P Q) k X)
    (hmin : ∀ C' : HeterogeneousAvoidCover P
      (heterogeneousTailNormalize P Q) k X,
      C.D.card ≤ C'.D.card)
    (hxD : base ∈ C.D)
    (n : ℕ) (hkn : k < n)
    (E : Finset U) :
    (∀ v ∈ E,
      v ∈ (P (Fin.last d)).carrier ∧ C.root ≤ v) →
    Nonempty (HeterogeneousAtScaleAvoidState P Q base n E) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨initialHeterogeneousAtScaleAvoidState P Q base hkn⟩
  | @insert v E hv ih =>
      intro hE
      have hOld : ∀ w ∈ E,
          w ∈ (P (Fin.last d)).carrier ∧ C.root ≤ w := by
        intro w hw
        exact hE w (Finset.mem_insert_of_mem hw)
      obtain ⟨S⟩ := ih hOld
      obtain ⟨hvCarrier, hrootv⟩ :=
        hE v (Finset.mem_insert_self v E)
      let m : ℕ := S.level + 1
      obtain ⟨y, hvy, hyC, _, hAvoid⟩ :=
        exists_heterogeneousAvoidWitness_above_of_minimal
          P (heterogeneousTailNormalize P Q)
          k C hmin hxD hvCarrier hrootv m
      obtain ⟨q, hq⟩ :=
        (P (Fin.last d)).carrier_levels y (C.Y_inside hyC)
      have hySource : y ∈ (P (Fin.last d)).sourceLevel q :=
        ⟨C.Y_inside hyC, hq⟩
      have hkm : k < m := by
        dsimp [m]
        exact S.baseBelowSupport.trans (Nat.lt_succ_self S.level)
      obtain ⟨M', l', hM'level, hM'dense, hM'above,
        hM'avoids, hM'below, hlevelGrow⟩ :=
        heterogeneousNormalizedRefinementStep
          P Q hd hstab base S.M (S.Y : Set U)
          S.onLevel S.dense S.aboveBase
          S.avoids S.belowSupport
          (Nat.lt_succ_self S.level) hkm y hySource hAvoid
      let Y' : Finset U := insert y S.Y
      refine ⟨{
        M := M'
        level := l'
        Y := Y'
        onLevel := hM'level
        dense := hM'dense
        aboveBase := hM'above
        avoids := ?_
        belowSupport := ?_
        covers := ?_
        baseBelowSupport := S.baseBelowSupport.trans hlevelGrow
      }⟩
      · intro z hz
        have hzSet : z ∈ Set.insert y (S.Y : Set U) := by
          rcases Finset.mem_insert.mp hz with rfl | hzOld
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_iff.mpr (Or.inr hzOld)
        exact hM'avoids z hzSet
      · intro z hz
        have hzSet : z ∈ Set.insert y (S.Y : Set U) := by
          rcases Finset.mem_insert.mp hz with rfl | hzOld
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_iff.mpr (Or.inr hzOld)
        exact hM'below z hzSet
      · intro z hz
        rcases Finset.mem_insert.mp hz with rfl | hzOld
        · exact ⟨y, Finset.mem_insert_self y S.Y, hvy⟩
        · obtain ⟨w, hwY, hzw⟩ := S.covers z hzOld
          exact ⟨w, Finset.mem_insert_of_mem hwY, hzw⟩

end GeneralTree
end Milliken
