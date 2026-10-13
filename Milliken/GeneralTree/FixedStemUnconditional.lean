import Milliken.GeneralTree.HeterogeneousUniversalMilliken
import Milliken.Applications.FiniteColour

/-!
# Fixed-stem finite-colouring Milliken for arbitrary locally finite trees

The homogeneous library already proves an anchored finite-colour
corollary from the topological Ramsey theorem on basic Ellentuck
neighbourhoods. Now that universal heterogeneous HDHL and the
unrestricted general-tree Milliken theorem are checked, the *same
argument* works for any pruned, finitely branching ambient tree.

The fixed stem consists of the first ell **selected source levels**,
never all nodes up to ambient height ell. The ambient degrees may
depend on the node and have no global bound.
-/

namespace Milliken
namespace GeneralTree

/-- Source-faithful anchored finite-colouring theorem for every
arbitrary locally finitely branching rooted ambient tree. It is
exactly the adaptation of Applications.millikenFixedStemFiniteColouring
from homogeneous List-alphabet strong embeddings to genuine general
strong subtrees and Todorčević's general approximation space.

For every finite colouring of height-k approximations, the output
retains the first ell source levels of A, and all infinite refinements
retaining this stem have the same height-k colour. -/
theorem millikenFixedStemFiniteColouring_general
    (U : AmbientTree)
    (ell k colors : ℕ) [NeZero colors]
    (A : StrongSubtree U)
    (colour : SFinite U k → Fin colors) :
    ∃ B : StrongSubtree U,
      B.Refines A ∧ r ell B = r ell A ∧
      ∀ X Y : StrongSubtree U,
        X.Refines B → Y.Refines B →
        r ell X = r ell A → r ell Y = r ell A →
        colour (r k X) = colour (r k Y) := by
  let S := generalApproximationSystem U
  have hne :
      (S.neighborhood (r ell A) A).Nonempty := by
    refine ⟨A, ?_⟩
    exact ⟨StrongSubtree.refines_refl A, rfl⟩
  obtain ⟨B, hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring_for_Milliken
      (generalMilliken_unconditional U)
      (r ell A) A hne colour
  refine ⟨B, hBA.1, hBA.2, ?_⟩
  intro X Y hXB hYB hX hY
  exact hhom X ⟨hXB, hX⟩ Y ⟨hYB, hY⟩

/-- Equivalent single-colour anchored statement. A representative
colour is chosen by evaluating the output tree B itself. -/
theorem millikenFixedStemMonochromatic_general
    (U : AmbientTree)
    (ell k colors : ℕ) [NeZero colors]
    (A : StrongSubtree U)
    (colour : SFinite U k → Fin colors) :
    ∃ B : StrongSubtree U, ∃ c : Fin colors,
      B.Refines A ∧ r ell B = r ell A ∧
      ∀ X : StrongSubtree U,
        X.Refines B → r ell X = r ell A →
        colour (r k X) = c := by
  obtain ⟨B, hBA, hStem, hhom⟩ :=
    millikenFixedStemFiniteColouring_general U ell k colors A colour
  refine ⟨B, colour (r k B), hBA, hStem, ?_⟩
  intro X hXB hX
  exact hhom X B hXB (StrongSubtree.refines_refl B) hX hStem

end GeneralTree
end Milliken
