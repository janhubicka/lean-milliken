import Milliken.GeneralTree.CodePoint
import Milliken.GeneralTree.BoundaryTupleHL
import RamseySpace.AbstractEllentuck

/-!
# Unrestricted general-tree Tychonoff closedness and conditional Milliken

Every full approximation code whose finite prefixes can be realised
by arbitrary strong subtrees reconstructs an actual infinite strong
subtree. Consequently the image of the general-tree approximation
map is closed in the literal Tychonoff product of discrete finite
approximations, with no homogeneous-alphabet or uniform degree bound.

Todorčević's Abstract Ellentuck theorem then yields the published
topological Ramsey-space conclusion directly from the *one remaining
combinatorial hypothesis*, heterogeneous product Halpern--Läuchli.
The conditional theorem below does NOT assert this still-unproved
general HL theorem as an axiom or established lemma.
-/

namespace Milliken
namespace GeneralTree

/-- The approximation image of every locally finite pruned strong-tree
space is closed, in the first-difference finite-prefix sense. -/
theorem generalIsMetricallyClosed (U : AmbientTree) :
    (generalApproximationSystem U).IsMetricallyClosed := by
  intro c hc
  have hprefix : ∀ N : ℕ, CodePrefixRealizable c N := by
    intro N
    obtain ⟨T, hT⟩ := hc N
    exact ⟨T, hT⟩
  refine ⟨pointOfGeneralCode c hprefix, ?_⟩
  intro n
  exact pointOfGeneralCode_approx c hprefix n

/-- Literal textbook Tychonoff closedness of the arbitrary
strong-tree approximation code image. -/
theorem generalIsTychonoffClosed (U : AmbientTree) :
    (generalApproximationSystem U).IsTychonoffClosed :=
  ((generalApproximationSystem U).
    isTychonoffClosed_iff_isClosedApproximationImage).2
      (generalIsMetricallyClosed U)

/-- The full published general-tree Milliken/Ellentuck conclusion,
conditional *only* on the standard heterogeneous finite-product HL
theorem. Closedness, A.1--A.3, and the exact A.4 reduction have
all been supplied by unconditional Lean theorems. -/
theorem generalMilliken_of_generalProductHL
    (U : AmbientTree)
    (hHL : HasGeneralProductHL U) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := generalApproximationSystem U) := by
  exact RamseySpace.abstractEllentuck_textbook
    (abstractRamseySpace_of_generalProductHL U hHL)
    (generalIsTychonoffClosed U)

/-- The depth-form topological Ramsey conclusion under the same
single heterogeneous HL hypothesis. -/
theorem generalMillikenDepth_of_generalProductHL
    (U : AmbientTree)
    (hHL : HasGeneralProductHL U) :
    RamseySpace.IsTopologicalRamseySpace
      (abstractRamseySpace_of_generalProductHL U hHL) := by
  exact RamseySpace.abstractEllentuck
    (abstractRamseySpace_of_generalProductHL U hHL)
    (generalIsMetricallyClosed U)

end GeneralTree
end Milliken
