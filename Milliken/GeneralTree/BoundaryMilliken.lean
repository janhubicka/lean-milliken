import Milliken.GeneralTree.GeneralClosed
import Milliken.GeneralTree.BoundaryTupleHL
import RamseySpace.AbstractEllentuck

/-!
# General-tree topological Milliken from precisely boundary-cone HL

The published arbitrary-tree one-step pigeonhole uses only the finite
product Halpern--Läuchli theorem for the actual successor cones of
each finite strong-tree stem. It need not assume the stronger
product-HL property for every artificially supplied vector of factors.

The theorem below applies the already verified canonical A.4 reduction,
A.1--A.3, and unrestricted Tychonoff closedness. The **only**
remaining premise is the standard *boundary-instance* heterogeneous
HL statement, which is explicitly still unproved in Lean.

This is a conditional implication, not an axiom or an unconditional
proof of that heterogeneous HL statement.
-/

namespace Milliken
namespace GeneralTree

/-- The textbook topological Ramsey/Milliken conclusion, conditional
only on finite-product Halpern--Läuchli for the genuine boundary
successor cones of arbitrary locally finitely branching trees. -/
theorem generalMilliken_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := generalApproximationSystem U) := by
  let R : RamseySpace.AbstractRamseySpace
      (generalApproximationSystem U) :=
    abstractRamseySpace_of_pigeonhole U
      (generalPigeonhole_of_boundaryProductHL U hHL)
  exact RamseySpace.abstractEllentuck_textbook R
    (generalIsTychonoffClosed U)

/-- Corresponding depth-form conclusion under exactly the same
genuine boundary-cone Halpern--Läuchli premise. -/
theorem generalMillikenDepth_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U) :
    RamseySpace.IsTopologicalRamseySpace
      (abstractRamseySpace_of_pigeonhole U
        (generalPigeonhole_of_boundaryProductHL U hHL)) := by
  exact RamseySpace.abstractEllentuck
    (abstractRamseySpace_of_pigeonhole U
      (generalPigeonhole_of_boundaryProductHL U hHL))
    (generalIsMetricallyClosed U)

end GeneralTree
end Milliken
