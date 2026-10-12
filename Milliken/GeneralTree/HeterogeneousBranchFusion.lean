import Milliken.GeneralTree.HeterogeneousFusionWitnesses
import Milliken.GeneralTree.ChosenStrong

/-!
# Monochromatic heterogeneous branch fusion

Choose one next-matrix node in each *actual ambient child cone* of
every retained parent. Off the protected base cones the choice
defaults to the canonical long-cone representative. The resulting
dependent recursion is a genuine strong subtree with source levels
given by the increasing matrix support indices, and every selected
source-level product is monochromatic. The colour can still depend
on the source index; extraction of an infinite constant-colour
subsequence is a separate step.

No fixed branching alphabet or uniform degree bound is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

namespace StrongSubtree

/-- An invariant of all chosen levels follows by induction from the
initial root and its preservation in each actual child cone. -/
theorem LevelChoice.level_property
    {B : StrongSubtree U} {f : ℕ → ℕ}
    (C : LevelChoice B f) (Q : ℕ → Set U)
    (hroot : C.root ∈ Q 0)
    (hstep : ∀ k (x : U) (hx : x ∈ B.sourceLevel (f k))
      (y : ChildIndex U x),
      x ∈ Q k → C.next k x hx y ∈ Q (k + 1)) :
    ∀ k (x : U), x ∈ C.level k → x ∈ Q k := by
  intro k
  induction k with
  | zero =>
      intro x hx
      rw [C.level_zero] at hx
      have heq : x = C.root := hx
      subst x
      exact hroot
  | succ k ih =>
      intro z hz
      obtain ⟨x, y, hEq⟩ := (C.level_succ_iff k z).mp hz
      rw [hEq]
      exact hstep k x.1 (C.level_subset_sourceLevel k x.2)
        y (ih x.1 x.2)

end StrongSubtree

/-- One first-matrix node above the fixed base exists in each
coordinate and lies on the common first support level. -/
theorem exists_heterogeneousFusionRoot
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) :
    ∃ z : U,
      z ∈ (P i).sourceLevel
        (heterogeneousFusionLevels P c hd base hall 0) ∧
      z ∈ (heterogeneousFusionWitnesses
        P c hd base hall 0).M.coord i ∧
      base.1 i ≤ z := by
  let W := heterogeneousFusionWitnesses P c hd base hall 0
  obtain ⟨x, hx, hbase⟩ :=
    (P i).exists_sourceLevel_descendant
      W.base_le_scale (base.2 i)
  obtain ⟨z, hz, hxz⟩ := W.dense i x hx hbase
  exact ⟨z, W.onLevel i z hz, hz, hbase.trans hxz⟩

noncomputable def heterogeneousFusionRoot
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) : U :=
  Classical.choose (exists_heterogeneousFusionRoot P c hd base hall i)

theorem heterogeneousFusionRoot_spec
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) :
    heterogeneousFusionRoot P c hd base hall i ∈
      (P i).sourceLevel (heterogeneousFusionLevels P c hd base hall 0) ∧
    heterogeneousFusionRoot P c hd base hall i ∈
      (heterogeneousFusionWitnesses P c hd base hall 0).M.coord i ∧
    base.1 i ≤ heterogeneousFusionRoot P c hd base hall i :=
  Classical.choose_spec
    (exists_heterogeneousFusionRoot P c hd base hall i)

/-- The next monochromatic matrix meets each immediate child
cone of a parent lying above the base. -/
theorem exists_heterogeneousFusionNext_in_matrix
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) (k : ℕ) (x : U)
    (hx : x ∈ (P i).sourceLevel
      (heterogeneousFusionLevels P c hd base hall k))
    (y : ChildIndex U x)
    (hbase : base.1 i ≤ x) :
    ∃ z : U,
      z ∈ (heterogeneousFusionWitnesses
        P c hd base hall (k + 1)).M.coord i ∧
      (y : U) ≤ z := by
  let W := heterogeneousFusionWitnesses P c hd base hall (k + 1)
  have hscale :
      heterogeneousFusionLevels P c hd base hall k < W.scale := by
    rw [heterogeneousFusionWitnesses_succ_scale]
    exact Nat.lt_succ_self _
  obtain ⟨t, ht, hyt⟩ :=
    (P i).exists_sourceLevel_descendant_in_childCone
      hscale hx y.2
  have hbaset : base.1 i ≤ t :=
    hbase.trans (y.2.le.trans hyt)
  obtain ⟨z, hz, htz⟩ := W.dense i t ht hbaset
  exact ⟨z, hz, hyt.trans htz⟩

/-- Total choice: a monochromatic witness when available,
otherwise the canonical long-cone representative. -/
noncomputable def heterogeneousFusionNext
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) (k : ℕ) (x : U)
    (hx : x ∈ (P i).sourceLevel
      (heterogeneousFusionLevels P c hd base hall k))
    (y : ChildIndex U x) : U := by
  classical
  let W := heterogeneousFusionWitnesses P c hd base hall (k + 1)
  exact if h : ∃ z : U, z ∈ W.M.coord i ∧ (y : U) ≤ z then
    Classical.choose h
  else
    (P i).longConeRepresentative
      (heterogeneousFusionLevels_strictMono P c hd base hall
        (Nat.lt_succ_self k)) hx y

theorem heterogeneousFusionNext_spec
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) (k : ℕ) (x : U)
    (hx : x ∈ (P i).sourceLevel
      (heterogeneousFusionLevels P c hd base hall k))
    (y : ChildIndex U x) :
    heterogeneousFusionNext P c hd base hall i k x hx y ∈
      (P i).sourceLevel
        (heterogeneousFusionLevels P c hd base hall (k + 1)) ∧
    (y : U) ≤
      heterogeneousFusionNext P c hd base hall i k x hx y := by
  classical
  dsimp only [heterogeneousFusionNext]
  split_ifs with h
  · have hh := Classical.choose_spec h
    exact ⟨(heterogeneousFusionWitnesses
      P c hd base hall (k + 1)).onLevel i _ hh.1, hh.2⟩
  · exact (P i).longConeRepresentative_spec
      (heterogeneousFusionLevels_strictMono
        P c hd base hall (Nat.lt_succ_self k)) hx y

theorem heterogeneousFusionNext_mem_of_base
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) (k : ℕ) (x : U)
    (hx : x ∈ (P i).sourceLevel
      (heterogeneousFusionLevels P c hd base hall k))
    (y : ChildIndex U x)
    (hbase : base.1 i ≤ x) :
    heterogeneousFusionNext P c hd base hall i k x hx y ∈
      (heterogeneousFusionWitnesses
        P c hd base hall (k + 1)).M.coord i := by
  classical
  have hExists :=
    exists_heterogeneousFusionNext_in_matrix
      P c hd base hall i k x hx y hbase
  unfold heterogeneousFusionNext
  simp only [dif_pos hExists]
  exact (Classical.choose_spec hExists).1

/-- A genuine LevelChoice indexed by the same support sequence
in each heterogeneous coordinate. -/
noncomputable def heterogeneousFusionLevelChoice
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) :
    StrongSubtree.LevelChoice
      (P i) (heterogeneousFusionLevels P c hd base hall) where
  root := heterogeneousFusionRoot P c hd base hall i
  root_mem := (heterogeneousFusionRoot_spec P c hd base hall i).1
  next := fun k x hx y =>
    heterogeneousFusionNext P c hd base hall i k x hx y
  next_mem := by
    intro k x hx y
    exact (heterogeneousFusionNext_spec
      P c hd base hall i k x hx y).1
  next_above := by
    intro k x hx y
    exact (heterogeneousFusionNext_spec
      P c hd base hall i k x hx y).2

/-- Every selected node lies above the fixed base and inside
the corresponding monochromatic matrix coordinate. -/
theorem heterogeneousFusionLevelChoice_level_spec
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) (k : ℕ) (x : U)
    (hx : x ∈
      (heterogeneousFusionLevelChoice P c hd base hall i).level k) :
    x ∈ (heterogeneousFusionWitnesses
        P c hd base hall k).M.coord i ∧
      base.1 i ≤ x := by
  let C := heterogeneousFusionLevelChoice P c hd base hall i
  let Q : ℕ → Set U :=
    fun k => {z | z ∈ (heterogeneousFusionWitnesses
      P c hd base hall k).M.coord i ∧ base.1 i ≤ z}
  have hroot : C.root ∈ Q 0 :=
    (heterogeneousFusionRoot_spec P c hd base hall i).2
  have hnext :
      ∀ k (z : U)
        (hz : z ∈ (P i).sourceLevel
          (heterogeneousFusionLevels P c hd base hall k))
        (y : ChildIndex U z),
        z ∈ Q k → C.next k z hz y ∈ Q (k + 1) := by
    intro n z hz y hzQ
    constructor
    · exact heterogeneousFusionNext_mem_of_base
        P c hd base hall i n z hz y hzQ.2
    · exact hzQ.2.trans (y.2.le.trans
        (heterogeneousFusionNext_spec
          P c hd base hall i n z hz y).2)
  exact C.level_property Q hroot hnext k x hx

/-- Every common source-level product of generated trees
is monochromatic, with the colour of its matrix witness. -/
theorem heterogeneousFusionLevel_monochromatic
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (k : ℕ) (x : Fin d → U)
    (hx : ∀ i,
      x i ∈ (heterogeneousFusionLevelChoice
        P c hd base hall i).level k) :
    c x = (heterogeneousFusionWitnesses
      P c hd base hall k).color := by
  apply (heterogeneousFusionWitnesses P c hd base hall k).monochromatic
  intro i
  exact (heterogeneousFusionLevelChoice_level_spec
    P c hd base hall i k (x i) (hx i)).1

/-- The actual-child-cone fusion yields strong refinements
with common source support indices. -/
noncomputable def heterogeneousFusionTrees
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    Fin d → StrongSubtree U :=
  fun i =>
    (heterogeneousFusionLevelChoice P c hd base hall i).toStrongSubtree
      (heterogeneousFusionLevels_strictMono P c hd base hall)

theorem heterogeneousFusionTrees_refines
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) :
    (heterogeneousFusionTrees P c hd base hall i).Refines (P i) :=
  (heterogeneousFusionLevelChoice P c hd base hall i).toStrongSubtree_refines
    (heterogeneousFusionLevels_strictMono P c hd base hall)

theorem heterogeneousFusionTrees_levels
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (i : Fin d) :
    (heterogeneousFusionTrees P c hd base hall i).levels =
      fun k => (P i).levels (heterogeneousFusionLevels
        P c hd base hall k) :=
  (heterogeneousFusionLevelChoice P c hd base hall i).toStrongSubtree_levels
    (heterogeneousFusionLevels_strictMono P c hd base hall)

theorem heterogeneousFusionTrees_monochromatic_at
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2) (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q, HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (k : ℕ) (x : Fin d → U)
    (hx : ∀ i, x i ∈
      (heterogeneousFusionTrees P c hd base hall i).sourceLevel k) :
    c x = (heterogeneousFusionWitnesses P c hd base hall k).color := by
  apply heterogeneousFusionLevel_monochromatic
    P c hd base hall k x
  intro i
  have hi := hx i
  simpa only [heterogeneousFusionTrees,
    StrongSubtree.LevelChoice.toStrongSubtree_sourceLevel] using hi

end GeneralTree
end Milliken
