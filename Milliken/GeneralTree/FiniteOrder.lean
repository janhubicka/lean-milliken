import Milliken.GeneralTree.ApproximationSystem
import Mathlib.Data.Set.Finite.Powerset

/-!
# A.2: finite approximation lower cones at a fixed source height

No global bound on the branching of the ambient tree is needed:
every finite approximation has a finite node carrier, and an approximation
of a *fixed* source height is uniquely determined by that carrier.
Therefore all such approximations contained in a given finite carrier
form a finite family.

The full A.2 lower-finiteness property for the Sigma-type over ALL
source heights still requires an additional argument bounding the height
by the size of the carrier. This file explicitly does not claim A.2
is complete.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- There are finitely many realised finite strong subtrees of a fixed
source height whose carriers are included in a fixed finite set. -/
theorem boundedApprox_finite
    {B : Set U} (hB : B.Finite) (n : ℕ) :
    {a : SFinite U n | a.carrier ⊆ B}.Finite := by
  classical
  letI : Finite {C : Set U // C ⊆ B} :=
    hB.finite_subsets.to_subtype
  let encode :
      {a : SFinite U n // a.carrier ⊆ B} →
        {C : Set U // C ⊆ B} :=
    fun a => ⟨a.1.carrier, a.2⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply FiniteApprox.ext_carrier
    exact congrArg Subtype.val hab
  exact Finite.of_injective encode hencode

/-- The published finite order (6.3) has finitely many predecessors
of each fixed height, below any given finite approximation. -/
theorem bookLeFin_fixedHeight_lowerFinite
    (b : Σ m, SFinite U m) (n : ℕ) :
    {a : SFinite U n | bookLeFin ⟨n, a⟩ b}.Finite := by
  have hB : (b.2.carrier).Finite := b.2.carrier_finite
  apply (boundedApprox_finite (U := U) hB n).subset
  intro a ha
  exact (bookLeFin_iff.mp ha).1

end GeneralTree
end Milliken
