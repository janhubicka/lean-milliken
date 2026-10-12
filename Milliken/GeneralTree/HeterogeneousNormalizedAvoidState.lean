import Milliken.GeneralTree.HeterogeneousNormalizedRefinement
import Milliken.GeneralTree.HeterogeneousMinimalAvoid

/-!
# Finite successor recursion in heterogeneous Lemma 3.15

The branching degree depends on the node.  This proof inducts over a
finite set of actual ambient children, never a common alphabet.
Each stage retains a dense level matrix inside the fixed front cones,
keeps it beyond every last-coordinate section parameter, and avoids
all previously selected tail-normalized sections.

All inputs are proved lemmas about strong trees, minimum avoiding
covers, tail normalization and matrix refinement.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- State after processing a finite set E of actual ambient children. -/
structure HeterogeneousNormalizedAvoidState
    {d k : ℕ}
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (s : ℕ) (E : Finset U) where
  M : HeterogeneousMatrix (fun i : Fin d => P i.castSucc)
  level : ℕ
  Y : Finset U
  onLevel : M.OnLevel level
  dense : M.DenseAbove base.1 (s + 1)
  aboveBase : ∀ z ∈ M.carrier, ∀ i, base.1 i ≤ z i
  avoids : ∀ y ∈ Y,
    M.carrier ⊆
      (heterogeneousLastSection (heterogeneousTailNormalize P Q) y)ᶜ
  belowSupport : ∀ y ∈ Y,
    ∃ q : ℕ, y ∈ (P (Fin.last d)).sourceLevel q ∧ q < level
  covers : ∀ c ∈ E, ∃ y ∈ Y, c ≤ y
  baseBelowSupport : k < level

/-- The complete source level s+1, restricted above the base tuple. -/
noncomputable def initialHeterogeneousNormalizedAvoidState
    {d k s : ℕ}
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (hks : k ≤ s) :
    HeterogeneousNormalizedAvoidState P Q base s ∅ := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  let F : HeterogeneousMatrix Front :=
    HeterogeneousMatrix.fullLevel Front (s + 1)
  let M : HeterogeneousMatrix Front :=
    F.restrictAbove base.1
  exact {
    M := M
    level := s + 1
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
      intro c hc
      simp at hc
    baseBelowSupport := by omega
  }

/-- The finite recursion hidden in equation (3) of Todorčević's
Lemma 3.15, for heterogeneous locally finitely branching trees. -/
theorem exists_heterogeneousNormalizedAvoidState
    {d k s : ℕ}
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
    (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel s)
    (hroot : C.root ≤ t)
    (hks : k ≤ s)
    (E : Finset U) :
    (∀ c ∈ E, t ⋖ c) →
      Nonempty (HeterogeneousNormalizedAvoidState P Q base s E) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      intro _
      exact ⟨initialHeterogeneousNormalizedAvoidState
        P Q base hks⟩
  | @insert c E hc ih =>
      intro hE
      have hOld : ∀ z ∈ E, t ⋖ z := by
        intro z hz
        exact hE z (Finset.mem_insert_of_mem hz)
      obtain ⟨S⟩ := ih hOld
      have htc : t ⋖ c :=
        hE c (Finset.mem_insert_self c E)
      obtain ⟨v, hv, _⟩ :=
        (P (Fin.last d)).successor_unique s t
          ht.1 ht.2 c htc
      have hvCarrier : v ∈ (P (Fin.last d)).carrier :=
        hv.1
      have hcv : c ≤ v := hv.2.2
      have hrootv : C.root ≤ v :=
        hroot.trans (htc.le.trans hcv)
      let n : ℕ := S.level + 1
      obtain ⟨y, hvy, hyC, _, hAvoid⟩ :=
        exists_heterogeneousAvoidWitness_above_of_minimal
          P (heterogeneousTailNormalize P Q)
          k C hmin hxD hvCarrier hrootv n
      obtain ⟨q, hq⟩ :=
        (P (Fin.last d)).carrier_levels y (C.Y_inside hyC)
      have hySource : y ∈ (P (Fin.last d)).sourceLevel q :=
        ⟨C.Y_inside hyC, hq⟩
      have hkn : k < n := by
        dsimp [n]
        exact S.baseBelowSupport.trans (Nat.lt_succ_self S.level)
      obtain ⟨M', l', hM'level, hM'dense, hM'above,
        hM'avoids, hM'below, hlevelGrow⟩ :=
        heterogeneousNormalizedRefinementStep
          P Q hd hstab base S.M (S.Y : Set U)
          S.onLevel S.dense S.aboveBase
          S.avoids S.belowSupport
          (Nat.lt_succ_self S.level) hkn y hySource hAvoid
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
        · exact ⟨y, Finset.mem_insert_self y S.Y, hcv.trans hvy⟩
        · obtain ⟨w, hwY, hzw⟩ := S.covers z hzOld
          exact ⟨w, Finset.mem_insert_of_mem hwY, hzw⟩

end GeneralTree
end Milliken
