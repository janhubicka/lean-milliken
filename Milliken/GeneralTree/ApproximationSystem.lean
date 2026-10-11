import Milliken.GeneralTree.Vector
import Milliken.GeneralTree.Coherence
import RamseySpace.Basic

/-!
# A.1 approximation systems for arbitrary locally finite trees

This packages the proved geometry as two instances of the exact A.1
`RamseySpace.ApproximationSystem` interface used by the checked abstract
Ellentuck library. The scalar system works for *any* pruned locally
finitely branching rooted ambient tree, with no global degree bound.

The vector system works for a positive-dimensional finite vector of such
trees, with one common selected level map. The dimension condition is
essential for separation: when there are no coordinates, finite
approximations cannot observe the stored level sequence.

A.2 finitisation, A.3 amalgamation, A.4 pigeonhole and closedness are
NOT claimed by these definitions; a full general-tree Milliken theorem
would require all those additional proofs.
-/

namespace Milliken
namespace GeneralTree

/-- A.1: the approximation system of infinite strong subtrees of an
arbitrary pruned, locally finitely branching rooted ambient tree. -/
def generalApproximationSystem
    (U : AmbientTree) : RamseySpace.ApproximationSystem where
  Point := SInfinity U
  Approx := SFinite U
  le := fun S T => S.Refines T
  le_refl := by
    intro S
    exact StrongSubtree.refines_refl S
  le_trans := by
    intro S T R hST hTR
    exact StrongSubtree.refines_trans hST hTR
  approx := fun n S => r n S
  approx_surjective := fun n => r_surjective (U := U) n
  empty := r 0 (identityStrongSubtree U)
  approx_zero := by
    intro S
    exact r_zero_eq S (identityStrongSubtree U)
  separated := by
    intro S T h
    exact r_separated h
  coherent := by
    intro S T n h m hm
    exact r_coherent_le S T n h m hm.le

/-- The A.1 basic neighbourhood is precisely the published
strong-tree neighbourhood `[a,T]`. -/
theorem generalNeighborhood_eq
    (U : AmbientTree) (n : ℕ) (a : SFinite U n)
    (T : SInfinity U) :
    (generalApproximationSystem U).neighborhood a T =
      BasicNeighborhood a T := by
  rfl

/-- Canonical identity synchronized vector strong tree.
It needs one coordinate to make the common level sequence observable
from the vector carriers. -/
def identityVectorStrongSubtree
    {d : ℕ} (U : Fin d → AmbientTree) (hd : 0 < d) :
    StrongVectorSubtree U where
  coordinate := fun i => identityStrongSubtree (U i)
  levels := fun n => n
  levels_strictMono := strictMono_id
  synchronized := by
    intro i
    rfl
  dimension_pos := hd

/-- A.1 for finite synchronized vectors of arbitrary pruned locally
finitely branching rooted ambient trees. -/
def vectorApproximationSystem
    {d : ℕ} (U : Fin d → AmbientTree) (hd : 0 < d) :
    RamseySpace.ApproximationSystem where
  Point := StrongVectorSubtree U
  Approx := FiniteVectorApprox U
  le := fun S T => S.Refines T
  le_refl := by
    intro S
    exact StrongVectorSubtree.refines_refl S
  le_trans := by
    intro S T R hST hTR
    exact StrongVectorSubtree.refines_trans hST hTR
  approx := fun n S => vectorApprox n S
  approx_surjective := fun n => vectorApprox_surjective (U := U) n
  empty := vectorApprox 0 (identityVectorStrongSubtree U hd)
  approx_zero := by
    intro S
    exact vectorApprox_zero_eq S (identityVectorStrongSubtree U hd)
  separated := by
    intro S T h
    exact vectorApprox_separated h
  coherent := by
    intro S T n h m hm
    exact vectorApprox_coherent h hm.le

/-- Vector Ellentuck basic neighbourhoods are the published
fixed-prefix vector refinement neighbourhoods. -/
theorem vectorNeighborhood_eq
    {d : ℕ} (U : Fin d → AmbientTree) (hd : 0 < d)
    (n : ℕ) (a : FiniteVectorApprox U n)
    (T : StrongVectorSubtree U) :
    (vectorApproximationSystem U hd).neighborhood a T =
      VectorBasicNeighborhood a T := by
  rfl

end GeneralTree
end Milliken
