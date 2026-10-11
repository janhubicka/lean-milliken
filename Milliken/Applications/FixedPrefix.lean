import Milliken.Applications.Original1979

/-!
# Fixed-initial-level formulation of finite Milliken

This is the `Str_{ell,k}`-style API used in applications. For `ell ≤ k`,
the restriction of a height-`k` finite strong subtree to its first `ell`
**source** levels is another finite strong subtree, not a truncation at
ambient height `ell`.

The theorem below directly colors all finite height-`k` strong subtrees
inside a selected homogeneous infinite strong subtree *with the first
ell source levels fixed*. The variable-branching vector-tree transport is
not supplied here.
-/

namespace Milliken
namespace Applications

universe u v

/-- Restrict a realised height-`k` finite strong subtree to its first
`ell` source levels, for `ell ≤ k`. -/
def truncateApprox {ι : Type u} {ell k : Nat}
    (h : ell ≤ k) (a : StrongTreeSpace.Approx ι k) :
    StrongTreeSpace.Approx ι ell :=
  ⟨(fun s => a.1 ⟨s.1, lt_of_lt_of_le s.2 h⟩),
    (by
      obtain ⟨X, hX⟩ := a.2
      refine ⟨X, ?_⟩
      intro s
      exact hX ⟨s.1, lt_of_lt_of_le s.2 h⟩)⟩

@[simp] theorem truncateApprox_approx
    {ι : Type u} {ell k : Nat} (h : ell ≤ k)
    (X : StrongEmbedding ι) :
    truncateApprox h (StrongTreeSpace.approx ι k X) =
      StrongTreeSpace.approx ι ell X := by
  apply Subtype.ext
  funext s
  rfl

/-- Truncating first to an intermediate level and then further is the
same as restricting directly. -/
theorem truncateApprox_trans
    {ι : Type u} {ell mid k : Nat}
    (h₁ : ell ≤ mid) (h₂ : mid ≤ k)
    (a : StrongTreeSpace.Approx ι k) :
    truncateApprox h₁ (truncateApprox h₂ a) =
      truncateApprox (h₁.trans h₂) a := by
  apply Subtype.ext
  funext s
  rfl

/-- The direct finite strong-subtree version of fixed-stem Milliken on a
homogeneous ambient tree. All height-`k` strong subtrees contained in
`B` and having the prescribed first `ell` source levels receive
one color. Neither the stem nor the ambient root is assumed at level zero.
-/
theorem millikenFixedStem1979_homogeneous
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (ell k : Nat) (h : ell ≤ k)
    (A : StrongEmbedding ι)
    (colour : StrongTreeSpace.Approx ι k → κ) :
    ∃ B : StrongEmbedding ι,
      StrongTreeSpace.le ι B A ∧
      StrongTreeSpace.approx ι ell B =
        StrongTreeSpace.approx ι ell A ∧
      ∃ c : κ,
        ∀ a : StrongTreeSpace.Approx ι k,
          StrongTreeSpace.approxCarrier a ⊆ StrongEmbedding.range B →
          truncateApprox h a = StrongTreeSpace.approx ι ell A →
          colour a = c := by
  obtain ⟨B, hBA, hBstem, hhom⟩ :=
    millikenFixedStemFiniteColouring ell k A colour
  refine ⟨B, hBA, hBstem,
    colour (StrongTreeSpace.approx ι k B), ?_⟩
  intro a ha hstem
  obtain ⟨X, hXB, hXa⟩ := exists_refinement_realising a B ha
  have hXstem :
      StrongTreeSpace.approx ι ell X =
        StrongTreeSpace.approx ι ell A := by
    calc
      StrongTreeSpace.approx ι ell X =
          truncateApprox h (StrongTreeSpace.approx ι k X) :=
            (truncateApprox_approx h X).symm
      _ = truncateApprox h a := congrArg (truncateApprox h) hXa
      _ = StrongTreeSpace.approx ι ell A := hstem
  rw [← hXa]
  exact hhom X B hXB (StrongTreeSpace.le_refl ι B)
    hXstem hBstem

end Applications
end Milliken
