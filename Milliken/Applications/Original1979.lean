import Milliken.Applications.FiniteColour
import Milliken.StemExtension

/-!
# Milliken 1979: colour finite strong subtrees

A realised finite approximation is exactly a finite strong subtree of the
homogeneous ambient tree. An approximation with carrier inside an infinite
strong subtree can be extended to a strong embedding through that tree.
This file turns the infinite-refinement statement into a direct coloring of
*all* height-k finite strong subtrees contained in a chosen infinite tree.

This is the homogeneous-ambient-tree case of Milliken's 1979 theorem.
For general rooted, finitely branching ambient trees with unbounded degree,
a new variable-branching transfer theorem is still required.
-/

namespace Milliken
namespace Applications

universe u v

/-- A finite strong subtree (represented as a realised approximation) is
contained in an infinite strong subtree precisely when its carrier is in the
range. This lemma constructs an infinite refinement realising that finite
subtree. For height zero the unique empty approximation is realised by
every strong embedding. -/
theorem exists_refinement_realising
    {ι : Type u} [Nonempty ι] {k : Nat}
    (a : StrongTreeSpace.Approx ι k)
    (B : StrongEmbedding ι)
    (h : StrongTreeSpace.approxCarrier a ⊆ StrongEmbedding.range B) :
    ∃ X : StrongEmbedding ι,
      StrongTreeSpace.le ι X B ∧
        StrongTreeSpace.approx ι k X = a := by
  cases k with
  | zero =>
      obtain ⟨A, ha⟩ := StrongTreeSpace.approx_surjective ι 0 a
      refine ⟨B, StrongTreeSpace.le_refl ι B, ?_⟩
      calc
        StrongTreeSpace.approx ι 0 B =
            StrongTreeSpace.empty ι := StrongTreeSpace.approx_zero ι B
        _ = StrongTreeSpace.approx ι 0 A :=
            (StrongTreeSpace.approx_zero ι A).symm
        _ = a := ha
  | succ k =>
      let Z := StrongTreeSpace.stemExtension
        (Nat.zero_lt_succ k) a B h
      refine ⟨StrongEmbedding.comp B Z, ⟨Z, rfl⟩, ?_⟩
      exact StrongTreeSpace.approx_comp_stemExtension
        (Nat.zero_lt_succ k) a B h

/-- Milliken's original finite-colour conclusion for a homogeneous ambient
tree: every height-k finite strong subtree whose nodes lie in the selected
infinite strong subtree has one common colour. Valid also at k = 0. -/
theorem milliken1979_homogeneous
    {ι : Type u} [Finite ι] [Nonempty ι]
    {κ : Type v} [Fintype κ]
    (k : Nat) (colour : StrongTreeSpace.Approx ι k → κ) :
    ∃ B : StrongEmbedding ι, ∃ c : κ,
      ∀ a : StrongTreeSpace.Approx ι k,
        StrongTreeSpace.approxCarrier a ⊆ StrongEmbedding.range B →
          colour a = c := by
  obtain ⟨B, hB⟩ := millikenFiniteColouring k colour
  refine ⟨B, colour (StrongTreeSpace.approx ι k B), ?_⟩
  intro a ha
  obtain ⟨X, hXB, hXa⟩ := exists_refinement_realising a B ha
  rw [← hXa]
  exact hB X B hXB (StrongTreeSpace.le_refl ι B)

end Applications
end Milliken
