import Milliken.GeneralTree.HeterogeneousMarkedBoundaryGraft
import Milliken.GeneralTree.HeterogeneousBinaryStrongHL

/-!
# A local section-stabilization step for heterogeneous strong trees

Assuming heterogeneous HDHL in the *same front dimension* for
every finite family of its genuine cone factors, binary strong-tree
Halpern--Läuchli selects refinements of the marked boundary cones
on which the chosen colour set is constant at every common level.

The synchronized marked-boundary graft fills the other cones,
keeps the first n source levels, and puts the selected refinements
exactly in the desired sectors. This yields a new synchronized
family and a genuine new source-n base tuple above the old one,
such that membership in the colour set is constant on every
later common product-level tuple extending that base.

This is one local stabilization requirement, NOT yet the
finite-requirement fusion or its infinite limit. It works for
actual node-dependent, unbounded finite branching.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A set is constant above one genuine source-level boundary
tuple of a synchronized finite product of strong trees. -/
def HeterogeneousConeConstant
    (P : Fin d → StrongSubtree U)
    (A : Set (Fin d → U))
    {n : ℕ} (base : HeterogeneousLevelTuple P n) : Prop :=
  ∀ l : ℕ, ∀ z : HeterogeneousLevelTuple P l,
    n ≤ l →
      (∀ i, base.1 i ≤ z.1 i) →
        (z.1 ∈ A ↔ base.1 ∈ A)

/-- A single local stabilizing refinement at a prescribed
source-level boundary, using only front-dimensional HDHL and
the genuine synchronized boundary graft. -/
theorem exists_heterogeneousLocalConeStabilization
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (n : ℕ)
    (base : HeterogeneousLevelTuple P n)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (A : Set (Fin d → U)) :
    ∃ (LM : ℕ → ℕ) (S : Fin d → StrongSubtree U)
      (b : HeterogeneousLevelTuple S n),
      StrictMono LM ∧
        (∀ i, (S i).Refines (P i) ∧
          r n (S i) = r n (P i) ∧
          (S i).levels = LM) ∧
        (∀ i, base.1 i ≤ b.1 i) ∧
        HeterogeneousConeConstant S A b := by
  classical
  let B : Fin d → StrongSubtree U :=
    heterogeneousBoundaryCones P n base
  let LB : ℕ → ℕ := fun k => L (n + k)
  have hB : ∀ i, (B i).levels = LB :=
    heterogeneousBoundaryCones_levels P n base L hP
  let colour : (Fin d → U) → Fin 2 :=
    fun z => if z ∈ A then 1 else 0
  obtain ⟨chosen, M, R, hM, hR, hmono⟩ :=
    heterogeneousBinarySynchronizedHL_of_hdhl
      B hd (hAll B) LB hB colour
  have hRB :
      ∀ i, (R i).Refines
        (heterogeneousBoundaryCones P n base i) := by
    intro i
    exact (hR i).1
  have hRlevels : ∀ i, (R i).levels = M :=
    fun i => (hR i).2
  obtain ⟨S, hS, hSector, hSelectedRoot⟩ :=
    exists_synchronizedMarkedBoundaryGraft
      P hd n base L M hP R hRlevels hRB
  let i0 : Fin d := ⟨0, hd⟩
  let LM : ℕ → ℕ := (S i0).levels
  have hSync : ∀ i, (S i).levels = LM := by
    intro i
    have hi := (hS i).2.1
    have h0 := (hS i0).2.1
    change (S i).levels = (S i0).levels
    rw [hi, h0]
    funext k
    by_cases hk : k < n
    · rw [(P i).boundaryGraftLevels_before n M hk,
          (P i0).boundaryGraftLevels_before n M hk]
      exact (congrFun (hP i) k).trans
        (congrFun (hP i0) k).symm
    · simp only [StrongSubtree.boundaryGraftLevels, hk,
        ↓reduceIte]
  have hLM : StrictMono LM := (S i0).levels_strictMono
  let b : HeterogeneousLevelTuple S n :=
    ⟨fun i => (R i).root, hSelectedRoot⟩
  have hbOld : ∀ i, base.1 i ≤ b.1 i := by
    intro i
    exact (hRB i (R i).root_mem).2
  have hconst : HeterogeneousConeConstant S A b := by
    intro l z hnl hbz
    have hRz :
        ∀ i, z.1 i ∈ (R i).sourceLevel (l - n) := by
      intro i
      have hzR : z.1 i ∈ (R i).carrier :=
        hSector i (z.1 i) (z.2 i).1
          ((hbOld i).trans (hbz i))
      have hSL : (S i).levels l = M (l - n) := by
        calc
          (S i).levels l =
              (P i).boundaryGraftLevels n M l :=
            congrFun (hS i).2.1 l
          _ = M (l - n) := by
            have hh := (P i).boundaryGraftLevels_at
              n M (l - n)
            have hl : n + (l - n) = l := by omega
            rw [hl] at hh
            exact hh
      refine ⟨hzR, ?_⟩
      calc
        U.level (z.1 i) = (S i).levels l := (z.2 i).2
        _ = M (l - n) := hSL
        _ = (R i).levels (l - n) :=
          (congrFun (hRlevels i) (l - n)).symm
    have hRb : ∀ i, b.1 i ∈ (R i).sourceLevel 0 := by
      intro i
      exact ⟨(R i).root_mem, (R i).root_level⟩
    have hcz : colour z.1 = chosen :=
      hmono (l - n) z.1 hRz
    have hcb : colour b.1 = chosen :=
      hmono 0 b.1 hRb
    have hcEq : colour z.1 = colour b.1 :=
      hcz.trans hcb.symm
    constructor
    · intro hzA
      by_contra hbNot
      simp [colour, hzA, hbNot] at hcEq
    · intro hbA
      by_contra hzNot
      simp [colour, hbA, hzNot] at hcEq
  refine ⟨LM, S, b, hLM, ?_, hbOld, hconst⟩
  intro i
  exact ⟨(hS i).1, (hS i).2.2, hSync i⟩

end GeneralTree
end Milliken
