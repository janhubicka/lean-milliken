import Milliken.HalpernLauchli.StabilizationFinite
import Milliken.HalpernLauchli.FiniteWitness

/-!
# Stabilizing one last-coordinate level

At stage `k` of the fusion we process every last-coordinate node on level
`k` and every front boundary vector on level `k+1`.  There are only
finitely many such pairs.  The finite fusion from the previous file therefore
produces one front-coordinate refinement for which the stabilization identity
holds for every last-coordinate node on level `k`.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Stabilization restricted to last-coordinate nodes on one fixed level. -/
def StabilizedAtLevel {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) : Prop :=
  ∀ (y : Node ι), y.length = k →
    ∀ (l : ℕ) (x : Fin d → Node ι),
      IsLevelVectorAt l x →
      k < l →
        (x ∈ lastSection P y ↔
          truncateVector (k + 1) x ∈ lastSection P y)

/-- All local requirements at stage `k`. -/
noncomputable def stageRequirements
    [Finite ι]
    (d k : ℕ) :
    List (BoundaryRequirement ι d (k + 1)) := by
  classical
  letI : Finite (treeLevel (ι := ι) k) :=
    finite_treeLevel k
  letI : Fintype (treeLevel (ι := ι) k) :=
    Fintype.ofFinite _
  letI : Finite (LevelVector ι d (k + 1)) :=
    finite_levelVector d (k + 1)
  letI : Fintype (LevelVector ι d (k + 1)) :=
    Fintype.ofFinite _
  exact
    ((Finset.univ :
        Finset (treeLevel (ι := ι) k)).product
      (Finset.univ :
        Finset (LevelVector ι d (k + 1)))).toList.map
      (fun p => ⟨p.1.1, p.2⟩)

theorem mem_stageRequirements
    [Finite ι]
    (d k : ℕ)
    (y : treeLevel (ι := ι) k)
    (x : LevelVector ι d (k + 1)) :
    (⟨y.1, x⟩ :
      BoundaryRequirement ι d (k + 1)) ∈
        stageRequirements d k := by
  classical
  letI : Finite (treeLevel (ι := ι) k) :=
    finite_treeLevel k
  letI : Fintype (treeLevel (ι := ι) k) :=
    Fintype.ofFinite _
  letI : Finite (LevelVector ι d (k + 1)) :=
    finite_levelVector d (k + 1)
  letI : Fintype (LevelVector ι d (k + 1)) :=
    Fintype.ofFinite _
  simp [stageRequirements]

/-- Constancy on all level-`k+1` boundary cones is exactly the
stabilization identity for last-coordinate level `k`. -/
theorem stabilizedAtLevel_of_requirements
    [Finite ι]
    {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    (hall :
      ∀ R ∈ stageRequirements (ι := ι) d k,
        SatisfiesRequirement P R) :
    StabilizedAtLevel P k := by
  intro y hy l z hzlevel hkl
  have hsucc : k + 1 ≤ l := by omega
  let base : Fin d → Node ι :=
    truncateVector (k + 1) z
  have hbaseLevel :
      IsLevelVectorAt (k + 1) base := by
    dsimp [base]
    exact truncateVector_length hzlevel hsucc
  let x : LevelVector ι d (k + 1) :=
    ⟨base, hbaseLevel⟩
  let yt : treeLevel (ι := ι) k :=
    ⟨y, hy⟩
  let R : BoundaryRequirement ι d (k + 1) :=
    ⟨y, x⟩
  have hmem :
      R ∈ stageRequirements (ι := ι) d k := by
    dsimp [R, yt, x]
    exact mem_stageRequirements d k yt x
  have hconst := hall R hmem
  unfold SatisfiesRequirement at hconst
  have hpref :
      ∀ i, (x.1 i).IsPrefix (z i) := by
    intro i
    dsimp [x, base, truncateVector]
    exact List.take_prefix _ _
  have hiff :=
    hconst l z hzlevel hpref
  simpa [R, x, base] using hiff

/-- One complete stage of the stabilization fusion. -/
theorem exists_stage_refinement
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) :
    ∃ levels : ℕ → ℕ,
      ∃ F : Fin d → StrongEmbedding ι,
        HasCommonLevels F levels ∧
        PreservesBoundary (k + 1) F ∧
        FixesBelow (k + 1) F ∧
        StabilizedAtLevel (pullbackFront P F) k := by
  rcases exists_requirements_refinement
      hd hHDHL P (stageRequirements (ι := ι) d k) with
    ⟨levels, F, hcommon, hboundary, hfix, hall⟩
  refine ⟨levels, F, hcommon, hboundary, hfix, ?_⟩
  exact stabilizedAtLevel_of_requirements hall

end HalpernLauchli
end Milliken
