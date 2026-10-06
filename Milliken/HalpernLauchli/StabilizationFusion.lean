import Milliken.HalpernLauchli.StabilizationStage

/-!
# Iterating stabilization stages

A stage-`n` refinement fixes every source node below height `n+1`.
Consequently it preserves all stabilization identities obtained at earlier
last-coordinate levels.  This file packages that observation and builds the
finite fusion sequence whose `n`th member is stabilized at every level
below `n`.

The later diagonal-limit file only has to use the adjacent agreement supplied
here.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Fixing all nodes below a later height implies preservation of every
earlier boundary prefix. -/
theorem preservesBoundary_of_fixesBelow
    {d n m : ℕ}
    {F : Fin d → StrongEmbedding ι}
    (hnm : n < m)
    (hfix : FixesBelow m F) :
    PreservesBoundary n F := by
  intro i s hs
  let p : Node ι := s.take n
  have hplen : p.length = n := by
    dsimp [p]
    exact List.length_take_of_le hs
  have hplt : p.length < m := by
    rw [hplen]
    exact hnm
  have hfixp : (F i).toFun p = p :=
    hfix i p hplt
  have hpref : p.IsPrefix s := by
    dsimp [p]
    exact List.take_prefix _ _
  have himg :
      p.IsPrefix ((F i).toFun s) := by
    rw [← hfixp]
    exact (F i).prefix_mono hpref
  have heq :=
    List.prefix_iff_eq_take.mp himg
  change ((F i).toFun s).take n = s.take n
  dsimp [p] at heq
  rw [List.length_take_of_le hs] at heq
  exact heq.symm

/-- Stabilization at level `k` is equivalently cone constancy above every
front boundary vector on level `k+1`. -/
theorem constantAbove_of_stabilizedAtLevel
    {d k : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : StabilizedAtLevel P k)
    (y : Node ι) (hy : y.length = k)
    (x : LevelVector ι d (k + 1)) :
    ConstantAbove (lastSection P y) x := by
  intro l z hzlevel hxz
  have hkl : k < l := by
    let i0 : Fin d := ⟨0, hd⟩
    have hlen := (hxz i0).length_le
    rw [x.2 i0, hzlevel i0] at hlen
    omega
  have htrunc :
      truncateVector (k + 1) z = x.1 := by
    funext i
    dsimp [truncateVector]
    have heq :=
      List.prefix_iff_eq_take.mp (hxz i)
    rw [x.2 i] at heq
    exact heq.symm
  have h := hstab y hy l z hzlevel hkl
  rw [htrunc] at h
  exact h

/-- A common-level refinement which preserves the boundary at height
`k+1` preserves stabilization at last-coordinate level `k`. -/
theorem stabilizedAtLevel_pullback
    [Nonempty ι]
    {d k : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : StabilizedAtLevel P k)
    {F : Fin d → StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hcommon : HasCommonLevels F levels)
    (hboundary : PreservesBoundary (k + 1) F) :
    StabilizedAtLevel (pullbackFront P F) k := by
  intro y hy l z hzlevel hkl
  let base : Fin d → Node ι :=
    truncateVector (k + 1) z
  have hbaseLevel :
      IsLevelVectorAt (k + 1) base := by
    dsimp [base]
    exact truncateVector_length hzlevel (by omega)
  let x : LevelVector ι d (k + 1) :=
    ⟨base, hbaseLevel⟩
  have hconst :
      ConstantAbove (lastSection P y) x :=
    constantAbove_of_stabilizedAtLevel
      hd hstab y hy x
  have hconst' :
      ConstantAbove
        (pullbackProduct F (lastSection P y)) x :=
    constantAbove_pullback
      hd hconst hcommon hboundary
  have hpref :
      ∀ i, (x.1 i).IsPrefix (z i) := by
    intro i
    dsimp [x, base, truncateVector]
    exact List.take_prefix _ _
  have hiff :=
    hconst' l z hzlevel hpref
  rw [mem_lastSection_pullbackFront P F y z,
      mem_lastSection_pullbackFront P F y
        (truncateVector (k + 1) z)]
  simpa [x, base] using hiff

/-- The cumulative state after solving all stabilization stages below `n`. -/
structure StabilizationFusionState
    (ι : Type u) (d : ℕ)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) where
  F : Fin d → StrongEmbedding ι
  levels : ℕ → ℕ
  common : HasCommonLevels F levels
  stabilized :
    ∀ k, k < n →
      StabilizedAtLevel (pullbackFront P F) k

/-- Initial stage: no stabilization requirements have yet been imposed. -/
def initialStabilizationFusionState
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    StabilizationFusionState ι d P 0 := {
  F := idFamily d
  levels := fun n => n
  common := idFamily_commonLevels d
  stabilized := by
    intro k hk
    omega
}

/-- One cumulative fusion step, retaining the factor used at this stage so
that adjacent approximations can later be shown to agree. -/
structure StabilizationFusionStep
    (ι : Type u) {d n : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    (S : StabilizationFusionState ι d P n) where
  next : StabilizationFusionState ι d P (n + 1)
  factor : Fin d → StrongEmbedding ι
  factorLevels : ℕ → ℕ
  factorCommon : HasCommonLevels factor factorLevels
  factorFixes : FixesBelow (n + 1) factor
  nextFamily :
    next.F = compFamily S.F factor

/-- A stage refinement extends any cumulative state and preserves all earlier
stabilization identities. -/
theorem exists_stabilizationFusionStep
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : StabilizationFusionState ι d P n) :
    Nonempty (StabilizationFusionStep ι S) := by
  classical
  rcases exists_stage_refinement
      hd hHDHL (pullbackFront P S.F) n with
    ⟨g, G, hGcommon, hGboundary, hGfix, hstage⟩
  let H : Fin d → StrongEmbedding ι :=
    compFamily S.F G
  let h : ℕ → ℕ :=
    fun m => S.levels (g m)
  have hHcommon : HasCommonLevels H h := by
    dsimp [H, h]
    exact compFamily_commonLevels S.common hGcommon
  have hHstab :
      ∀ k, k < n + 1 →
        StabilizedAtLevel (pullbackFront P H) k := by
    intro k hk
    by_cases hkn : k = n
    · subst k
      have hcomp :=
        pullbackFront_comp P S.F G
      dsimp [H]
      rw [← hcomp]
      exact hstage
    · have hkold : k < n := by omega
      have hold := S.stabilized k hkold
      have hlower :
          PreservesBoundary (k + 1) G :=
        preservesBoundary_of_fixesBelow
          (by omega) hGfix
      have hpres :=
        stabilizedAtLevel_pullback
          hd hold hGcommon hlower
      have hcomp :=
        pullbackFront_comp P S.F G
      dsimp [H]
      rw [← hcomp]
      exact hpres
  let T : StabilizationFusionState ι d P (n + 1) := {
    F := H
    levels := h
    common := hHcommon
    stabilized := hHstab
  }
  refine ⟨{
    next := T
    factor := G
    factorLevels := g
    factorCommon := hGcommon
    factorFixes := hGfix
    nextFamily := rfl
  }⟩

/-- Canonically choose one cumulative fusion step. -/
noncomputable def nextStabilizationFusionStep
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : StabilizationFusionState ι d P n) :
    StabilizationFusionStep ι S :=
  Classical.choice
    (exists_stabilizationFusionStep hd hHDHL S)

/-- The finite fusion sequence. -/
noncomputable def stabilizationFusionState
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    (n : ℕ) → StabilizationFusionState ι d P n
  | 0 => initialStabilizationFusionState P
  | n + 1 =>
      (nextStabilizationFusionStep
        hd hHDHL (stabilizationFusionState hd hHDHL P n)).next

/-- One fusion step does not change any source node lying below its protected
height. -/
theorem stabilizationFusionStep_agrees
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : StabilizationFusionState ι d P n)
    (i : Fin d) (s : Node ι)
    (hs : s.length < n + 1) :
    ((nextStabilizationFusionStep
      hd hHDHL S).next.F i).toFun s =
      (S.F i).toFun s := by
  let step :=
    nextStabilizationFusionStep hd hHDHL S
  have hfamily := congrFun step.nextFamily i
  rw [hfamily]
  change
    (S.F i).toFun ((step.factor i).toFun s) =
      (S.F i).toFun s
  rw [step.factorFixes i s hs]

/-- Adjacent members of the canonical fusion sequence agree below the new
protected height. -/
theorem stabilizationFusionState_succ_agrees
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin d) (s : Node ι)
    (hs : s.length < n + 1) :
    ((stabilizationFusionState
      hd hHDHL P (n + 1)).F i).toFun s =
      ((stabilizationFusionState
        hd hHDHL P n).F i).toFun s := by
  exact stabilizationFusionStep_agrees
    hd hHDHL
    (stabilizationFusionState hd hHDHL P n)
    i s hs

end HalpernLauchli
end Milliken
