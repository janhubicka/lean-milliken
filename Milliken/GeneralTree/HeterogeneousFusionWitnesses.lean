import Milliken.GeneralTree.HeterogeneousStrongSubtreePrep
import Milliken.GeneralTree.HeterogeneousNormalizedRefinement

/-!
# Coherent density/support sequence for heterogeneous HL fusion

From a fixed source-level product base above which arbitrarily
dense monochromatic matrices exist, choose a sequence of common
source-level-supported matrices. The next matrix is made dense
at exactly one source index above its predecessor's support.

The selected matrix supports therefore strictly increase, and
every stage records its own monochromatic colour. This is the
pure density arithmetic from Todorčević's strong-subtree proof;
the independent child-cone geometry and final colour subsequence
are constructed in separate modules.

All source levels belong to the actual heterogeneous input trees.
No common alphabet or global finite branching degree is assumed.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Monochromatic matrix selected at a prescribed source index,
together with the supporting level and growth inequality. -/
structure HeterogeneousFusionWitness
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    {r : ℕ}
    (base : HeterogeneousLevelTuple P r) where
  scale : ℕ
  base_le_scale : r ≤ scale
  color : Fin 2
  M : HeterogeneousMatrix P
  level : ℕ
  onLevel : M.OnLevel level
  dense : M.DenseAbove base.1 scale
  monochromatic : ∀ x ∈ M.carrier, c x = color
  scale_le_level : scale ≤ level

/-- Every high-enough density target has a corresponding
monochromatic common-support witness. -/
theorem exists_heterogeneousFusionWitness
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (q : ℕ) (hrq : r ≤ q)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    ∃ W : HeterogeneousFusionWitness P c base,
      W.scale = q := by
  obtain ⟨color, M, l, hLevel, hDense, hmono⟩ := hall q
  let W : HeterogeneousFusionWitness P c base := {
    scale := q
    base_le_scale := hrq
    color := color
    M := M
    level := l
    onLevel := hLevel
    dense := hDense
    monochromatic := hmono
    scale_le_level :=
      heterogeneous_support_ge_of_onLevel_denseAbove
        P hd base hrq M hLevel hDense
  }
  exact ⟨W, rfl⟩

/-- Choose a witness with the requested density scale. -/
noncomputable def heterogeneousChosenFusionWitness
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (q : ℕ) (hrq : r ≤ q)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    HeterogeneousFusionWitness P c base :=
  Classical.choose
    (exists_heterogeneousFusionWitness P c hd base q hrq hall)

theorem heterogeneousChosenFusionWitness_scale
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (q : ℕ) (hrq : r ≤ q)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    (heterogeneousChosenFusionWitness P c hd base q hrq hall).scale = q :=
  Classical.choose_spec
    (exists_heterogeneousFusionWitness P c hd base q hrq hall)

/-- An infinite tower of level matrices: the first is dense
one selected source level beyond the fixed base, and every
next is dense one selected source level beyond the previous
matrix support. -/
noncomputable def heterogeneousFusionWitnesses
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    ℕ → HeterogeneousFusionWitness P c base
  | 0 =>
      heterogeneousChosenFusionWitness P c hd base (r + 1)
        (Nat.le_succ r) hall
  | n + 1 =>
      let W := heterogeneousFusionWitnesses P c hd base hall n
      heterogeneousChosenFusionWitness P c hd base (W.level + 1)
        (W.base_le_scale.trans
          (W.scale_le_level.trans (Nat.le_succ W.level)))
        hall

/-- Supporting source index of the nth common monochromatic
level-matrix witness. -/
noncomputable def heterogeneousFusionLevels
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) : ℕ :=
  (heterogeneousFusionWitnesses P c hd base hall n).level

@[simp] theorem heterogeneousFusionWitnesses_zero_scale
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    (heterogeneousFusionWitnesses P c hd base hall 0).scale =
      r + 1 := by
  unfold heterogeneousFusionWitnesses
  exact heterogeneousChosenFusionWitness_scale
    P c hd base (r + 1) (Nat.le_succ r) hall

@[simp] theorem heterogeneousFusionWitnesses_succ_scale
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) :
    (heterogeneousFusionWitnesses P c hd base hall (n + 1)).scale =
      heterogeneousFusionLevels P c hd base hall n + 1 := by
  unfold heterogeneousFusionWitnesses
  exact heterogeneousChosenFusionWitness_scale
    P c hd base
      ((heterogeneousFusionWitnesses P c hd base hall n).level + 1)
      ((heterogeneousFusionWitnesses P c hd base hall n).base_le_scale.trans
        ((heterogeneousFusionWitnesses P c hd base hall n).scale_le_level.trans
          (Nat.le_succ
            (heterogeneousFusionWitnesses P c hd base hall n).level)))
      hall

/-- Each chosen supporting source index is strictly greater
than its predecessor. -/
theorem heterogeneousFusionLevels_lt_succ
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) :
    heterogeneousFusionLevels P c hd base hall n <
      heterogeneousFusionLevels P c hd base hall (n + 1) := by
  let W :=
    heterogeneousFusionWitnesses P c hd base hall (n + 1)
  have h := W.scale_le_level
  rw [heterogeneousFusionWitnesses_succ_scale] at h
  exact Nat.lt_of_succ_le h

theorem heterogeneousFusionLevels_strictMono
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hd : 0 < d)
    {r : ℕ} (base : HeterogeneousLevelTuple P r)
    (hall : ∀ q : ℕ,
      HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    StrictMono (heterogeneousFusionLevels P c hd base hall) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact heterogeneousFusionLevels_lt_succ P c hd base hall n

end GeneralTree
end Milliken
