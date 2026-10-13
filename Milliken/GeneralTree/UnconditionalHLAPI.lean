import Milliken.GeneralTree.HeterogeneousUniversalMilliken

/-!
# Unconditional Halpern–Läuchli and Ramsey-space application interfaces

The all-dimensional, all-ambient heterogeneous HDHL induction has
been checked without a uniform branching bound. The library already
contains the strong-product-HL, finite-boundary, canonical pigeonhole
and Abstract Ellentuck reductions. Here we export concise
*unconditional* named endpoints for downstream applications.

No new induction or combinatorial principle is used.
-/

namespace Milliken
namespace GeneralTree

/-- Strong-subtree product Halpern–Läuchli for arbitrary pruned,
locally finitely branching rooted ambient trees. The coordinate
strong trees may have different roots and branching patterns but
are synchronized by the common selected ambient-level sequence. -/
theorem generalProductHL_unconditional (U : AmbientTree) :
    HasGeneralProductHL U :=
  generalProductHL_of_all_heterogeneousHDHL U
    (fun d P hd => heterogeneousHDHL_unconditional d hd U P)

/-- The precise finite family of actual successor cones needed for
Todorčević's canonical one-step pigeonhole is now also unconditional. -/
theorem boundaryProductHL_unconditional (U : AmbientTree) :
    HasBoundaryProductHL U :=
  boundaryProductHL_of_generalProductHL U
    (generalProductHL_unconditional U)

/-- Canonical general-tree A.4 pigeonhole property with no remaining
heterogeneous HL theorem premise. -/
theorem generalPigeonhole_unconditional (U : AmbientTree) :
    HasGeneralPigeonhole U :=
  generalPigeonhole_of_generalProductHL U
    (generalProductHL_unconditional U)

/-- An unconditional abstract Ramsey-space instance for the
published general-tree approximation system; the full topological
Ramsey-space statement follows from checked general closedness. -/
def generalAbstractRamseySpace_unconditional (U : AmbientTree) :
    RamseySpace.AbstractRamseySpace
      (generalApproximationSystem U) :=
  abstractRamseySpace_of_generalProductHL U
    (generalProductHL_unconditional U)

end GeneralTree
end Milliken
