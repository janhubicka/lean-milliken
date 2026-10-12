import Milliken.GeneralTree.HeterogeneousLemma316Proof
import Milliken.AmbientChild

/-!
# The final stabilized heterogeneous HDHL induction step

Given the front-dimensional heterogeneous HDHL theorem,
Todorčević Lemma 3.16 supplies a dense positive section above every
last-tree node. We process the *actual finite set of ambient children*
of the last-tree root, not labels from a common branching alphabet.

At each stage a new common-level matrix is refined over the old one.
Stabilization preserves membership in all previously chosen sections.
The final finite list of last-coordinate witnesses is dense at source
index one, and its product with the front matrix lies in the target
colour class Q.

This proves the last stabilized part of the induction, under the
explicit stabilization and no-complement-somewhere-dense reductions.
It does not silently assert that every colouring has already been
stabilized, or that HDHL is proved in higher dimensions.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A front matrix together with all positive last-coordinate
sections already processed. -/
structure HeterogeneousSectionFusionState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) where
  M : HeterogeneousMatrix (fun i : Fin d => P i.castSucc)
  level : ℕ
  Y : Set U
  Y_inside : Y ⊆ (P (Fin.last d)).carrier
  onLevel : M.OnLevel level
  denseOne : M.DenseAt 1
  level_pos : 0 < level
  Y_below : ∀ y ∈ Y,
    ∃ q : ℕ, y ∈ (P (Fin.last d)).sourceLevel q ∧ q < level
  sections : ∀ y ∈ Y,
    M.carrier ⊆ heterogeneousLastSection Q y

/-- Start with the complete source-level-one front matrix and no
last-coordinate sections. -/
noncomputable def initialHeterogeneousSectionFusionState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) :
    HeterogeneousSectionFusionState P Q := {
  M := HeterogeneousMatrix.fullLevel
    (fun i : Fin d => P i.castSucc) 1
  level := 1
  Y := ∅
  Y_inside := by simp
  onLevel := HeterogeneousMatrix.fullLevel_onLevel _ 1
  denseOne := HeterogeneousMatrix.fullLevel_denseAt _ 1
  level_pos := by omega
  Y_below := by simp
  sections := by simp
}

/-- A step retaining all old section witnesses, and covering the
specified ambient child by a *genuine source-level-one representative*
below its new section node. -/
structure HeterogeneousSectionFusionStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (S : HeterogeneousSectionFusionState P Q)
    (c : U) where
  next : HeterogeneousSectionFusionState P Q
  oldY_subset : S.Y ⊆ next.Y
  covers_child :
    ∃ y ∈ next.Y, ∃ v : U,
      v ∈ (P (Fin.last d)).sourceLevel 1 ∧
        c ≤ v ∧ v ≤ y

/-- One actual ambient child can be processed while preserving
density, support, positivity of every old section and strict
separation between earlier last-coordinate ranks and support. -/
theorem exists_heterogeneousSectionFusionStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL
      (fun i : Fin d => P i.castSucc))
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (S : HeterogeneousSectionFusionState P Q)
    (c : U) (hchild : (P (Fin.last d)).root ⋖ c) :
    Nonempty (HeterogeneousSectionFusionStep P Q S c) := by
  classical
  let T : StrongSubtree U := P (Fin.last d)
  obtain ⟨v, hv, _⟩ :=
    T.successor_unique 0 T.root T.root_mem T.root_level
      c hchild
  have hvSource : v ∈ T.sourceLevel 1 :=
    ⟨hv.1, hv.2.1⟩
  obtain ⟨t, ht, hvt⟩ :=
    T.exists_sourceLevel_descendant
      (Nat.succ_le_of_lt S.level_pos) hvSource
  obtain ⟨y, N, l, hty, ⟨q, hySource, hql⟩,
    hNlevel, hNdense, hNsub⟩ :=
    heterogeneousLemma316 P Q hd hHDHL hstab hno
      S.level S.level t ht
  have hSl : S.level ≤ l :=
    N.support_ge_of_onLevel_denseAt hd hNlevel hNdense
  let R : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc) :=
    S.M.refineOver N
  have hRlevel : R.OnLevel l :=
    HeterogeneousMatrix.refineOver_onLevel hNlevel
  have hRdense : R.DenseAt 1 :=
    HeterogeneousMatrix.refineOver_denseAt
      S.onLevel S.denseOne hNdense
  have hRsubN : R.carrier ⊆ N.carrier :=
    HeterogeneousMatrix.refineOver_carrier_subset_right S.M N
  let Y' : Set U := Set.insert y S.Y
  let Tnext : HeterogeneousSectionFusionState P Q := {
    M := R
    level := l
    Y := Y'
    Y_inside := by
      intro z hz
      rcases hz with rfl | hzOld
      · exact hySource.1
      · exact S.Y_inside hzOld
    onLevel := hRlevel
    denseOne := hRdense
    level_pos := S.level_pos.trans_le hSl
    Y_below := by
      intro z hz
      rcases hz with rfl | hzOld
      · exact ⟨q, hySource, hql⟩
      · obtain ⟨s, hzs, hsS⟩ := S.Y_below z hzOld
        exact ⟨s, hzs, hsS.trans_le hSl⟩
    sections := by
      intro z hz
      rcases hz with rfl | hzOld
      · exact hRsubN.trans hNsub
      · obtain ⟨s, hzs, hsS⟩ := S.Y_below z hzOld
        exact HeterogeneousMatrix.refineOver_preserves_section
          P Q hstab hd z hzs S.onLevel hNlevel
          hsS (S.sections z hzOld)
  }
  refine ⟨{
    next := Tnext
    oldY_subset := ?_
    covers_child := ?_
  }⟩
  · intro z hz
    exact Or.inr hz
  · refine ⟨y, Or.inl rfl, v, hvSource, hv.2.2, ?_⟩
    exact hvt.trans hty

/-- Process an arbitrary finite collection of genuine ambient
immediate children of the last-tree root. Each processed child
retains its unique source-level-one representative below a positive
section node in the final state. -/
theorem exists_heterogeneousSectionFusionState
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL
      (fun i : Fin d => P i.castSucc))
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (E : Finset U) :
    (∀ c ∈ E, (P (Fin.last d)).root ⋖ c) →
      ∃ S : HeterogeneousSectionFusionState P Q,
        ∀ c ∈ E, ∃ y ∈ S.Y, ∃ v : U,
          v ∈ (P (Fin.last d)).sourceLevel 1 ∧
            c ≤ v ∧ v ≤ y := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨initialHeterogeneousSectionFusionState P Q, ?_⟩
      intro c hc
      simp at hc
  | @insert c E hc ih =>
      intro hE
      have hOld : ∀ z ∈ E,
          (P (Fin.last d)).root ⋖ z := by
        intro z hz
        exact hE z (Finset.mem_insert_of_mem hz)
      obtain ⟨S, hScovers⟩ := ih hOld
      obtain ⟨step⟩ :=
        exists_heterogeneousSectionFusionStep
          P Q hd hHDHL hstab hno S c
          (hE c (Finset.mem_insert_self c E))
      refine ⟨step.next, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hzOld
      · exact step.covers_child
      · obtain ⟨y, hyS, v, hv, hcv, hvy⟩ :=
          hScovers z hzOld
        exact ⟨y, step.oldY_subset hyS, v, hv, hcv, hvy⟩

/-- Final stabilized induction consequence: Q contains a globally
one-dense heterogeneous (d+1)-coordinate product matrix.

Only the proved front-dimensional HDHL, stabilization and the
no-complement-somewhere-dense reduction are premises. The finite
last-coordinate root branching is handled by its actual successor set,
which may have an arbitrarily large cardinality. -/
theorem heterogeneousExists_one_dense_of_stabilized
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL
      (fun i : Fin d => P i.castSucc))
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ) :
    ∃ M : HeterogeneousMatrix P,
      M.DenseAt 1 ∧ M.carrier ⊆ Q := by
  classical
  let T : StrongSubtree U := P (Fin.last d)
  let E : Finset U := (U.children_finite T.root).toFinset
  have hE : ∀ c ∈ E, T.root ⋖ c := by
    intro c hc
    change c ∈ (U.children_finite T.root).toFinset at hc
    change c ∈ U.children T.root
    simpa only [Set.Finite.mem_toFinset] using hc
  obtain ⟨S, hcover⟩ :=
    exists_heterogeneousSectionFusionState
      P Q hd hHDHL hstab hno E hE
  have hYdense :
      ∀ z ∈ T.sourceLevel 1,
        ∃ y, y ∈ S.Y ∧ z ≤ y := by
    intro z hz
    have hrootle : T.root ≤ z := T.root_below z hz.1
    rcases hrootle.eq_or_lt with heq | hlt
    · have heqlev : T.levels 0 = T.levels 1 := by
        calc
          T.levels 0 = U.level T.root := T.root_level.symm
          _ = U.level z := congrArg U.level heq
          _ = T.levels 1 := hz.2
      have hstrict := T.levels_strictMono
        (show 0 < 1 by omega)
      omega
    · obtain ⟨c, hchild, hcz⟩ := U.exists_child_le_of_lt hlt
      have hcE : c ∈ E := by
        change c ∈ (U.children_finite T.root).toFinset
        have hmem : c ∈ U.children T.root := hchild
        simpa only [Set.Finite.mem_toFinset] using hmem
      obtain ⟨y, hy, v, hv, hcv, hvy⟩ := hcover c hcE
      obtain ⟨w, hw, hunique⟩ :=
        T.successor_unique 0 T.root T.root_mem T.root_level
          c hchild
      have hzEq : z = w :=
        hunique z ⟨hz.1, hz.2, hcz⟩
      have hvEq : v = w :=
        hunique v ⟨hv.1, hv.2, hcv⟩
      have hzv : z = v := hzEq.trans hvEq.symm
      exact ⟨y, hy, by simpa only [hzv] using hvy⟩
  let M : HeterogeneousMatrix P :=
    S.M.snoc P S.Y S.Y_inside
  have hMdense : M.DenseAt 1 :=
    HeterogeneousMatrix.snoc_denseAt
      P S.M S.Y S.Y_inside 1 S.denseOne hYdense
  refine ⟨M, hMdense, ?_⟩
  intro z hz
  have hzpair :
      heteroFront z ∈ S.M.carrier ∧ heteroLast z ∈ S.Y := by
    apply (HeterogeneousMatrix.mem_snoc_carrier_appendLast
      P S.M S.Y S.Y_inside
      (heteroFront z) (heteroLast z)).mp
    rw [heteroAppendLast_front_last]
    exact hz
  have hzSection :
      heteroFront z ∈ heterogeneousLastSection Q (heteroLast z) :=
    S.sections (heteroLast z) hzpair.2 hzpair.1
  change heteroAppendLast (heteroFront z) (heteroLast z) ∈ Q
    at hzSection
  simpa only [heteroAppendLast_front_last] using hzSection

end GeneralTree
end Milliken
