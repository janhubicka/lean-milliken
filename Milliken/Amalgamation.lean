import Milliken.StemExtension
import RamseySpace.Axioms

/-!
# Amalgamation for the strong-subtree Ramsey space

The first half of Todorčević's A.3 is now a direct consequence of the
finite-stem extension constructor.  A depth witness places the carrier of the
finite approximation inside the first `d` levels of `B`; any
`A ∈ [d,B]` has exactly the same `d`th approximation, so the finite
carrier is also contained in `A).  We then pull the stem back through
`A` and extend it.

The refinement half A.3(2) is developed in the boundary-grafting file,
because the same graft is reused in the Halpern--Läuchli proof of A.4.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- Every finite approximation of a strong embedding lies in its range. -/
theorem approxCarrier_subset_range (X : StrongEmbedding ι) (d : ℕ) :
    approxCarrier (approx ι d X) ⊆ StrongEmbedding.range X := by
  rintro x ⟨s, rfl⟩
  exact ⟨s.1, rfl⟩

/-- A version of the preceding transfer lemma with an arbitrary tagged finite
approximation, matching the shape of a depth witness. -/
theorem carrier_subset_range_of_depth_main [Finite ι] [Nonempty ι]
    {n d : ℕ} (a : Approx ι n)
    (B A : StrongEmbedding ι)
    (hmain : (finitization (ι := ι)).leFin
      (⟨n, a⟩ : (S ι).FiniteApprox)
      ((S ι).finiteApprox d B))
    (hlevel : approx ι d A = approx ι d B) :
    approxCarrier a ⊆ StrongEmbedding.range A := by
  intro x hx
  have hxB :
      x ∈ approxCarrier (approx ι d B) :=
    hmain.2 hx
  have hxA :
      x ∈ approxCarrier (approx ι d A) := by
    rw [hlevel]
    exact hxB
  exact approxCarrier_subset_range A d hxA

/-- A.3(1): every depth-preserving refinement still admits an extension of
the prescribed finite strong subtree. -/
theorem amalgamation_nonempty [Finite ι] [Nonempty ι]
    {n : ℕ} (a : (S ι).Approx n) (B : (S ι).Point) {d : ℕ}
    (hd : (finitization (ι := ι)).HasDepth a B d) :
    ∀ ⦃A : (S ι).Point⦄, A ∈ (S ι).levelNeighborhood d B →
      ((S ι).neighborhood a A).Nonempty := by
  intro A hA
  have hcarrier :
      approxCarrier a ⊆ StrongEmbedding.range A :=
    carrier_subset_range_of_depth_main a B A hd.1 hA.2
  by_cases hn : n = 0
  · subst n
    have haA : approx ι 0 A = a := by
      rcases (S ι).approx_surjective 0 a with ⟨X, hX⟩
      calc
        approx ι 0 A = (S ι).empty := (S ι).approx_zero A
        _ = approx ι 0 X := ((S ι).approx_zero X).symm
        _ = a := hX
    exact ⟨A, (S ι).le_refl A, haA⟩
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    let E : StrongEmbedding ι :=
      stemExtension hpos a A hcarrier
    let X : StrongEmbedding ι :=
      StrongEmbedding.comp A E
    refine ⟨X, ?_, ?_⟩
    · exact ⟨E, rfl⟩
    · dsimp [X, E]
      exact approx_comp_stemExtension hpos a A hcarrier

end StrongTreeSpace
end Milliken
