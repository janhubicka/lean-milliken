import Milliken.MillikenTheorem
import Milliken.FiniteColourRamseySpace

/-!
# Homogeneous Milliken finite-colouring compatibility API

These statements use the original homogeneous `StrongEmbedding ι`
representation and are retained for existing clients. The generic
finite-colour Ramsey-space lemma now lives in a separate independent
module so unrestricted general-tree Milliken does not depend on the
homogeneous Hales--Jewett proof.
-/

namespace Milliken
namespace Applications

universe u v

/-- The concrete finite-colour formulation of homogeneous-tree Milliken.

Below the returned strong embedding `B`, every realized height-`m`
approximation has the same colour. -/
theorem millikenFiniteColouring
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (m : Nat)
    (colour : StrongTreeSpace.Approx ι m → κ) :
    ∃ B : StrongEmbedding ι,
      ∀ X Y : StrongEmbedding ι,
        StrongTreeSpace.le ι X B →
        StrongTreeSpace.le ι Y B →
        colour (StrongTreeSpace.approx ι m X) =
          colour (StrongTreeSpace.approx ι m Y) := by
  let S := StrongTreeSpace.approximationSystem ι
  have hne :
      (S.neighborhood (StrongTreeSpace.empty ι)
        (StrongEmbedding.id : StrongEmbedding ι)).Nonempty := by
    refine ⟨StrongEmbedding.id, ?_⟩
    exact ⟨StrongTreeSpace.le_refl ι _, StrongTreeSpace.approx_zero _ _⟩
  obtain ⟨B, hB, hhom⟩ :=
    RamseySpace.finiteApproximationColouring_for_Milliken
      (Milliken.Chapter6.milliken_onBasicNeighborhoods (ι := ι))
      (StrongTreeSpace.empty ι)
      (StrongEmbedding.id : StrongEmbedding ι)
      hne colour
  refine ⟨B, ?_⟩
  intro X Y hXB hYB
  have hX :
      X ∈ S.neighborhood (StrongTreeSpace.empty ι) B :=
    ⟨hXB, StrongTreeSpace.approx_zero ι X⟩
  have hY :
      Y ∈ S.neighborhood (StrongTreeSpace.empty ι) B :=
    ⟨hYB, StrongTreeSpace.approx_zero ι Y⟩
  exact hhom X hX Y hY


/-- A directly anchored finite-colour consequence of the fully
verified Milliken theorem on basic Ellentuck neighbourhoods. -/
theorem millikenFixedStemFiniteColouring
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (n m : Nat)
    (A : StrongEmbedding ι)
    (colour : StrongTreeSpace.Approx ι m → κ) :
    ∃ B : StrongEmbedding ι,
      StrongTreeSpace.le ι B A ∧
      StrongTreeSpace.approx ι n B =
        StrongTreeSpace.approx ι n A ∧
      ∀ X Y : StrongEmbedding ι,
        StrongTreeSpace.le ι X B →
        StrongTreeSpace.le ι Y B →
        StrongTreeSpace.approx ι n X =
          StrongTreeSpace.approx ι n A →
        StrongTreeSpace.approx ι n Y =
          StrongTreeSpace.approx ι n A →
        colour (StrongTreeSpace.approx ι m X) =
          colour (StrongTreeSpace.approx ι m Y) := by
  let S := StrongTreeSpace.approximationSystem ι
  let a := StrongTreeSpace.approx ι n A
  have hne : (S.neighborhood a A).Nonempty := by
    refine ⟨A, ?_⟩
    exact ⟨StrongTreeSpace.le_refl ι A, rfl⟩
  obtain ⟨B, hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring_for_Milliken
      (Milliken.Chapter6.milliken_onBasicNeighborhoods (ι := ι))
      a A hne colour
  refine ⟨B, hBA.1, hBA.2, ?_⟩
  intro X Y hXB hYB hX hY
  exact hhom X ⟨hXB, hX⟩ Y ⟨hYB, hY⟩


end Applications
end Milliken
