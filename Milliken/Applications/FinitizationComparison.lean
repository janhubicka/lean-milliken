import Milliken.FiniteApprox

/-!
# A regression witness: the proof-order finitisation is not literally (6.3)

Todorčević (6.3) requires inclusion of the maximal levels of the two
finite strong subtrees; the carrier+height order `leFin` used internally
to verify A.2 is strictly weaker as a *binary relation*.

These two relations may still induce the same **depth function** on
realised approximations below infinite strong trees. That comparison
requires a separate proof and is not asserted by this module.
-/

namespace Milliken
namespace StrongTreeSpace

/-- First one source level of the identity unary tree. -/
def comparisonOne : Σ n, Approx Unit n :=
  ⟨1, approx Unit 1 (StrongEmbedding.id : StrongEmbedding Unit)⟩

/-- First two source levels of the identity unary tree. -/
def comparisonTwo : Σ n, Approx Unit n :=
  ⟨2, approx Unit 2 (StrongEmbedding.id : StrongEmbedding Unit)⟩

/-- The first level is contained in the first two levels under the
carrier+height finitisation. -/
theorem comparison_leFin :
    leFin comparisonOne comparisonTwo := by
  constructor
  · decide
  · rintro x ⟨s, rfl⟩
    exact ⟨⟨s.1, lt_trans s.2 (by decide : 1 < 2)⟩, rfl⟩

/-- The same pair does NOT satisfy the published (6.3) finite order.
The maximal level of the one-level tree is the root, while the maximal
level of the two-level tree consists of depth-one nodes. -/
theorem comparison_not_bookLeFin :
    ¬ bookLeFin comparisonOne comparisonTwo := by
  intro h
  rcases h with hzero | ⟨_, _, hmax⟩
  · exact (by decide : (1 : ℕ) ≠ 0) hzero.1
  · have hnil :
        ([] : Node Unit) ∈
          approxMaxLevel
            (approx Unit 1 (StrongEmbedding.id : StrongEmbedding Unit)) :=
        ⟨⟨[], by decide⟩, by decide, rfl⟩
    obtain ⟨s, hs, hvalue⟩ := hmax hnil
    have hsource : s.1 = ([] : Node Unit) := by
      exact hvalue
    have hlength : s.1.length = 1 := by omega
    rw [hsource] at hlength
    simp at hlength

end StrongTreeSpace
end Milliken
