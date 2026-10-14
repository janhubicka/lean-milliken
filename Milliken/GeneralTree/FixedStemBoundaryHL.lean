import Milliken.GeneralTree.BoundaryMilliken
import Milliken.FiniteColourRamseySpace

/-!
# Protected-stem finite colouring from boundary Halpern–Läuchli

For applications that separate the combinatorial one-step
Halpern–Läuchli input from the Abstract Ellentuck conclusion, this
module gives the exact fixed-stem colouring implication without
assuming that the boundary product theorem has already been
specialised to the ambient tree.

The result is fully general: the ambient is any pruned locally finite
rooted tree; the colour type is an arbitrary finite type; and the
first `ell` selected source levels are protected. The unique
nontrivial premise is `HasBoundaryProductHL U`, which is proved
unconditionally elsewhere in this library.
-/

namespace Milliken
namespace GeneralTree

/-- From the finite successor-cone product Halpern–Läuchli property,
obtain a strong subtree retaining the specified first `ell` selected
source levels on which all refinements with that stem have one
height-`k` finite-approximation colour.

This uses the actual published basic-neighbourhood formulation,
rather than an application-specific scalar/vector encoding. -/
theorem millikenFixedStemFiniteColouring_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U)
    (ell k : ℕ) (A : StrongSubtree U)
    {κ : Type*} [Fintype κ]
    (colour : SFinite U k → κ) :
    ∃ B : StrongSubtree U,
      B.Refines A ∧ r ell B = r ell A ∧
      ∀ X Y : StrongSubtree U,
        X.Refines B → Y.Refines B →
        r ell X = r ell A → r ell Y = r ell A →
        colour (r k X) = colour (r k Y) := by
  let S := generalApproximationSystem U
  have hne : (S.neighborhood (r ell A) A).Nonempty :=
    ⟨A, StrongSubtree.refines_refl A, rfl⟩
  obtain ⟨B, hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      (generalMilliken_of_boundaryProductHL U hHL)
      (r ell A) A hne colour
  refine ⟨B, hBA.1, hBA.2, ?_⟩
  intro X Y hXB hYB hX hY
  exact hhom X ⟨hXB, hX⟩ Y ⟨hYB, hY⟩

end GeneralTree
end Milliken
