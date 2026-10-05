import Milliken.HalpernLauchli.StabilizationLimit

/-!
# Product-level stabilization fusion

The local stabilization lemmas refine the first `d` coordinates because
sections are taken in the last coordinate.  In Todorčević's proof, however,
after each fusion step all `d+1` trees are replaced by trees with the same
new level set.  Tracking this last-coordinate reindexing is essential for
preserving the meaning of "somewhere dense".

At a local stage the front refinements already share one level map.  Since
`d>0`, we use one of those same strong embeddings in the last coordinate.
It therefore has exactly the required level map and fixes the same protected
prefix.  This gives a genuine `d+1`-coordinate fusion while retaining the
front-only section argument as the local combinatorial lemma.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Append one strong embedding as the last member of a finite family. -/
def snocEmbeddingFamily {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (K : StrongEmbedding ι) :
    Fin (d + 1) → StrongEmbedding ι :=
  fun i => Fin.lastCases K (fun j => F j) i

theorem snocEmbeddingFamily_commonLevels
    {d : ℕ}
    {F : Fin d → StrongEmbedding ι}
    {K : StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hF : HasCommonLevels F levels)
    (hK : ∀ s : Node ι,
      (K.toFun s).length = levels s.length) :
    HasCommonLevels (snocEmbeddingFamily F K) levels := by
  refine ⟨hF.1, ?_⟩
  intro i s
  exact Fin.lastCases (hK s) (fun j => hF.2 j s) i

theorem snocEmbeddingFamily_fixesBelow
    {d n : ℕ}
    {F : Fin d → StrongEmbedding ι}
    {K : StrongEmbedding ι}
    (hF : FixesBelow n F)
    (hK : ∀ s : Node ι, s.length < n → K.toFun s = s) :
    FixesBelow n (snocEmbeddingFamily F K) := by
  intro i s hs
  exact Fin.lastCases (hK s hs) (fun j => hF j s hs) i

@[simp] theorem mapTuple_snocEmbeddingFamily_appendLast
    {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (K : StrongEmbedding ι)
    (x : Fin d → Node ι) (y : Node ι) :
    mapTuple (snocEmbeddingFamily F K) (appendLast x y) =
      appendLast (mapTuple F x) (K.toFun y) := by
  funext i
  exact Fin.lastCases rfl (fun _ => rfl) i

/-- Sections of a full product pullback are front pullbacks of the section
at the image of the last-coordinate node. -/
theorem mem_lastSection_pullbackProduct_snoc
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (F : Fin d → StrongEmbedding ι)
    (K : StrongEmbedding ι)
    (y : Node ι)
    (x : Fin d → Node ι) :
    x ∈ lastSection
        (pullbackProduct (snocEmbeddingFamily F K) P) y ↔
      x ∈ pullbackProduct F (lastSection P (K.toFun y)) := by
  change
    mapTuple (snocEmbeddingFamily F K) (appendLast x y) ∈ P ↔
      mapTuple F x ∈ lastSection P (K.toFun y)
  rw [mapTuple_snocEmbeddingFamily_appendLast]
  rfl

/-- If the last-coordinate refinement fixes level `k`, a front
stabilization at level `k` remains a stabilization after adjoining that
last-coordinate refinement. -/
theorem stabilizedAtLevel_pullback_snoc
    {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {F : Fin d → StrongEmbedding ι}
    {K : StrongEmbedding ι}
    (hfront : StabilizedAtLevel (pullbackFront P F) k)
    (hK : ∀ y : Node ι, y.length = k → K.toFun y = y) :
    StabilizedAtLevel
      (pullbackProduct (snocEmbeddingFamily F K) P) k := by
  intro y hy l x hxlevel hkl
  have hKy : K.toFun y = y := hK y hy
  have h := hfront y hy l x hxlevel hkl
  rw [mem_lastSection_pullbackFront P F y x,
      mem_lastSection_pullbackFront P F y
        (truncateVector (k + 1) x)] at h
  rw [mem_lastSection_pullbackProduct_snoc
        P F K y x,
      mem_lastSection_pullbackProduct_snoc
        P F K y (truncateVector (k + 1) x),
      hKy]
  exact h

/-- Cumulative product-level state after solving all last-coordinate levels
below `n`. -/
structure ProductStabilizationState
    (ι : Type u) (d : ℕ)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) where
  E : Fin (d + 1) → StrongEmbedding ι
  levels : ℕ → ℕ
  common : HasCommonLevels E levels
  stabilized :
    ∀ k, k < n →
      StabilizedAtLevel (pullbackProduct E P) k

/-- Initial product fusion state. -/
def initialProductStabilizationState
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    ProductStabilizationState ι d P 0 := {
  E := idFamily (d + 1)
  levels := fun n => n
  common := idFamily_commonLevels (d + 1)
  stabilized := by
    intro k hk
    omega
}

/-- One product-level fusion step and the relative family used in it. -/
structure ProductStabilizationStep
    (ι : Type u) {d n : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    (S : ProductStabilizationState ι d P n) where
  next : ProductStabilizationState ι d P (n + 1)
  factor : Fin (d + 1) → StrongEmbedding ι
  factorLevels : ℕ → ℕ
  factorCommon : HasCommonLevels factor factorLevels
  factorFixes : FixesBelow (n + 1) factor
  nextFamily :
    next.E = compFamily S.E factor

/-- One full product-level stage exists. -/
theorem exists_productStabilizationStep
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : ProductStabilizationState ι d P n) :
    Nonempty (ProductStabilizationStep ι S) := by
  classical
  let Q : Set (Fin (d + 1) → Node ι) :=
    pullbackProduct S.E P
  rcases exists_stage_refinement
      hd hHDHL Q n with
    ⟨g, G, hGcommon, hGboundary, hGfix, hstage⟩
  let i0 : Fin d := ⟨0, hd⟩
  let K : StrongEmbedding ι := G i0
  let R : Fin (d + 1) → StrongEmbedding ι :=
    snocEmbeddingFamily G K
  have hRcommon : HasCommonLevels R g := by
    dsimp [R, K]
    exact snocEmbeddingFamily_commonLevels
      hGcommon (hGcommon.2 i0)
  have hRfix : FixesBelow (n + 1) R := by
    dsimp [R, K]
    exact snocEmbeddingFamily_fixesBelow
      hGfix (hGfix i0)
  let H : Fin (d + 1) → StrongEmbedding ι :=
    compFamily S.E R
  let h : ℕ → ℕ :=
    fun m => S.levels (g m)
  have hHcommon : HasCommonLevels H h := by
    dsimp [H, h]
    exact compFamily_commonLevels S.common hRcommon
  have hHstab :
      ∀ k, k < n + 1 →
        StabilizedAtLevel (pullbackProduct H P) k := by
    intro k hk
    have hRstage :
        StabilizedAtLevel
          (pullbackProduct R Q) k := by
      by_cases hkn : k = n
      · subst k
        apply stabilizedAtLevel_pullback_snoc
          (P := Q) (F := G) (K := K) hstage
        intro y hy
        exact hGfix i0 y (by omega)
      · have hkold : k < n := by omega
        have hold : StabilizedAtLevel Q k :=
          S.stabilized k hkold
        have hlower :
            PreservesBoundary (k + 1) G :=
          preservesBoundary_of_fixesBelow
            (by omega) hGfix
        have hfront :
            StabilizedAtLevel (pullbackFront Q G) k :=
          stabilizedAtLevel_pullback
            hd hold hGcommon hlower
        apply stabilizedAtLevel_pullback_snoc
          (P := Q) (F := G) (K := K) hfront
        intro y hy
        exact hGfix i0 y (by omega)
    dsimp [H, Q] at hRstage ⊢
    rw [← pullbackProduct_comp S.E R P]
    exact hRstage
  let T : ProductStabilizationState ι d P (n + 1) := {
    E := H
    levels := h
    common := hHcommon
    stabilized := hHstab
  }
  refine ⟨{
    next := T
    factor := R
    factorLevels := g
    factorCommon := hRcommon
    factorFixes := hRfix
    nextFamily := rfl
  }⟩

/-- Canonical product-level step. -/
noncomputable def nextProductStabilizationStep
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : ProductStabilizationState ι d P n) :
    ProductStabilizationStep ι S :=
  Classical.choice
    (exists_productStabilizationStep hd hHDHL S)

/-- Finite product-level stabilization fusion. -/
noncomputable def productStabilizationState
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    (n : ℕ) → ProductStabilizationState ι d P n
  | 0 => initialProductStabilizationState P
  | n + 1 =>
      (nextProductStabilizationStep
        hd hHDHL (productStabilizationState hd hHDHL P n)).next

/-- One product fusion step fixes the protected finite source prefix. -/
theorem productStabilizationStep_agrees
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    {P : Set (Fin (d + 1) → Node ι)}
    (S : ProductStabilizationState ι d P n)
    (i : Fin (d + 1)) (s : Node ι)
    (hs : s.length < n + 1) :
    ((nextProductStabilizationStep
      hd hHDHL S).next.E i).toFun s =
      (S.E i).toFun s := by
  let step := nextProductStabilizationStep hd hHDHL S
  have hfamily := congrFun step.nextFamily i
  rw [hfamily]
  change
    (S.E i).toFun ((step.factor i).toFun s) =
      (S.E i).toFun s
  rw [step.factorFixes i s hs]

theorem productStabilizationState_succ_agrees
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin (d + 1)) (s : Node ι)
    (hs : s.length < n + 1) :
    ((productStabilizationState
      hd hHDHL P (n + 1)).E i).toFun s =
      ((productStabilizationState
        hd hHDHL P n).E i).toFun s := by
  exact productStabilizationStep_agrees
    hd hHDHL
    (productStabilizationState hd hHDHL P n)
    i s hs

end HalpernLauchli
end Milliken
