import Milliken.HalpernLauchli.FrontPullback

/-!
# Finite fusion of local stabilization requirements

At a fixed source boundary height there are only finitely many pairs
consisting of a last-coordinate node and a front level vector.  The
stabilization fusion processes these pairs one at a time.

A later local boundary graft preserves every cone-constancy property already
obtained at the same boundary height.  Consequently a finite list of local
requirements can be solved by ordinary recursion, while composing the
coordinate refinements.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- One section/boundary pair to be stabilized. -/
structure BoundaryRequirement (ι : Type u) (d n : ℕ) where
  y : Node ι
  x : LevelVector ι d n

/-- Constancy requirement associated with one section/boundary pair. -/
def SatisfiesRequirement
    {d n : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (R : BoundaryRequirement ι d n) : Prop :=
  ConstantAbove (lastSection P R.y) R.x

/-- Identity coordinate family. -/
def idFamily (d : ℕ) :
    Fin d → StrongEmbedding ι :=
  fun _ => StrongEmbedding.id

theorem idFamily_commonLevels (d : ℕ) :
    HasCommonLevels (idFamily (ι := ι) d) (fun n => n) := by
  refine ⟨strictMono_id, ?_⟩
  intro i s
  rfl

theorem idFamily_preservesBoundary
    {d n : ℕ} :
    PreservesBoundary n (idFamily (ι := ι) d) := by
  intro i s hs
  rfl

theorem idFamily_fixesBelow
    {d n : ℕ} :
    FixesBelow n (idFamily (ι := ι) d) := by
  intro i s hs
  rfl

/-- One global front-coordinate pullback solves one local requirement. -/
theorem exists_requirement_refinement
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (R : BoundaryRequirement ι d n) :
    ∃ levels : ℕ → ℕ,
      ∃ F : Fin d → StrongEmbedding ι,
        HasCommonLevels F levels ∧
        PreservesBoundary n F ∧
        FixesBelow n F ∧
        SatisfiesRequirement (pullbackFront P F) R := by
  rcases exists_stabilizationGraft
      hd hHDHL (lastSection P R.y) R.x with
    ⟨levels, F, hcommon, hboundary, hfix, hconst⟩
  refine ⟨levels, F, hcommon, hboundary, hfix, ?_⟩
  unfold SatisfiesRequirement
  have hsections :
      lastSection (pullbackFront P F) R.y =
        pullbackProduct F (lastSection P R.y) := by
    ext x
    exact mem_lastSection_pullbackFront P F R.y x
  rw [hsections]
  exact hconst

/-- A previously solved requirement survives a further refinement at the
same boundary height. -/
theorem requirement_preserved
    [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    {R : BoundaryRequirement ι d n}
    {F : Fin d → StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hR : SatisfiesRequirement P R)
    (hcommon : HasCommonLevels F levels)
    (hboundary : PreservesBoundary n F) :
    SatisfiesRequirement (pullbackFront P F) R := by
  unfold SatisfiesRequirement at hR ⊢
  have hsections :
      lastSection (pullbackFront P F) R.y =
        pullbackProduct F (lastSection P R.y) := by
    ext x
    exact mem_lastSection_pullbackFront P F R.y x
  rw [hsections]
  exact constantAbove_pullback
    hd hR hcommon hboundary

/-- Finite fusion at one boundary height. -/
theorem exists_requirements_refinement
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (requirements : List (BoundaryRequirement ι d n)) :
    ∃ levels : ℕ → ℕ,
      ∃ F : Fin d → StrongEmbedding ι,
        HasCommonLevels F levels ∧
        PreservesBoundary n F ∧
        FixesBelow n F ∧
        ∀ R ∈ requirements,
          SatisfiesRequirement (pullbackFront P F) R := by
  induction requirements generalizing P with
  | nil =>
      refine ⟨(fun m => m), idFamily d,
        idFamily_commonLevels d,
        idFamily_preservesBoundary,
        idFamily_fixesBelow, ?_⟩
      intro R hR
      simp at hR
  | cons R requirements ih =>
      rcases exists_requirement_refinement
          hd hHDHL P R with
        ⟨flevels, F, hFcommon, hFboundary,
          hFfix, hFR⟩
      let P₁ : Set (Fin (d + 1) → Node ι) :=
        pullbackFront P F
      rcases ih P₁ with
        ⟨glevels, G, hGcommon, hGboundary,
          hGfix, hGreq⟩
      let H : Fin d → StrongEmbedding ι :=
        compFamily F G
      let levels : ℕ → ℕ :=
        fun m => flevels (glevels m)
      have hHcommon : HasCommonLevels H levels := by
        dsimp [H, levels]
        exact compFamily_commonLevels hFcommon hGcommon
      have hHboundary : PreservesBoundary n H := by
        dsimp [H]
        exact compFamily_preservesBoundary
          hFboundary hGboundary
      have hHfix : FixesBelow n H := by
        dsimp [H]
        exact compFamily_fixesBelow hFfix hGfix
      refine ⟨levels, H, hHcommon,
        hHboundary, hHfix, ?_⟩
      intro Q hQ
      have hPull :
          pullbackFront P H =
            pullbackFront P₁ G := by
        dsimp [H, P₁]
        exact (pullbackFront_comp P F G).symm
      rcases hQ with rfl | hQtail
      · rw [hPull]
        exact requirement_preserved
          hd hFR hGcommon hGboundary
      · rw [hPull]
        exact hGreq Q hQtail

end HalpernLauchli
end Milliken
