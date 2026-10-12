import Milliken.GeneralTree.HeterogeneousLevelSupport

/-!
# Refining one heterogeneous dense matrix over another

Todorčević's Chapter 3 matrix-refinement step is not specific to a
single homogeneous alphabet. If A and B are coordinate matrices in
a finite product of actual strong subtrees, retain in B precisely
those nodes above a coordinate of A.

Level support and density are preserved by this operation.
Both global and cone-relative variants are proved, because the
higher-dimensional HDHL induction uses the latter while processing
successor cones one at a time.

No uniform bound on branching or fixed alphabet is assumed.
This is matrix geometry, not the unproved higher-dimensional HDHL.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ} {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- Keep each coordinate of B only above some coordinate of A. -/
def refineOver (A B : HeterogeneousMatrix P) :
    HeterogeneousMatrix P where
  coord := fun i => {z | z ∈ B.coord i ∧
    ∃ a ∈ A.coord i, a ≤ z}
  coord_sub := by
    intro i z hz
    exact B.coord_sub i hz.1

/-- Every node of the refined matrix belongs to the right matrix. -/
theorem refineOver_carrier_subset_right
    (A B : HeterogeneousMatrix P) :
    (A.refineOver B).carrier ⊆ B.carrier := by
  intro z hz i
  exact (hz i).1

/-- A refinement of a level-supported matrix has the same support level. -/
theorem refineOver_onLevel
    {A B : HeterogeneousMatrix P} {l : ℕ}
    (hB : B.OnLevel l) :
    (A.refineOver B).OnLevel l := by
  intro i z hz
  exact hB i z hz.1

/-- Every vector in the refined product has a coordinatewise
predecessor in the left matrix. -/
theorem exists_predecessor_of_mem_refineOver
    {A B : HeterogeneousMatrix P} {z : Fin d → U}
    (hz : z ∈ (A.refineOver B).carrier) :
    ∃ a ∈ A.carrier, ∀ i, a i ≤ z i := by
  classical
  choose a haA haz using fun i => (hz i).2
  exact ⟨a, (fun i => haA i), haz⟩

/-- A later globally l-dense matrix can be refined over a
level-l, k-dense matrix without losing k-density. -/
theorem refineOver_denseAt
    {A B : HeterogeneousMatrix P} {k l : ℕ}
    (hAlevel : A.OnLevel l)
    (hA : A.DenseAt k)
    (hB : B.DenseAt l) :
    (A.refineOver B).DenseAt k := by
  intro i x hx
  obtain ⟨a, haA, hxa⟩ := hA i x hx
  obtain ⟨z, hzB, haz⟩ :=
    hB i a (hAlevel i a haA)
  exact ⟨z, ⟨hzB, a, haA, haz⟩, hxa.trans haz⟩

/-- A later matrix dense in cones above a fixed base can be
refined over an earlier level-l matrix, retaining the earlier
cone density at k. -/
theorem refineOver_denseAbove
    {A B : HeterogeneousMatrix P}
    {base : Fin d → U} {k l : ℕ}
    (hAlevel : A.OnLevel l)
    (hA : A.DenseAbove base k)
    (hB : B.DenseAbove base l) :
    (A.refineOver B).DenseAbove base k := by
  intro i x hx hbasex
  obtain ⟨a, haA, hxa⟩ := hA i x hx hbasex
  obtain ⟨z, hzB, haz⟩ :=
    hB i a (hAlevel i a haA)
      (hbasex.trans hxa)
  exact ⟨z, ⟨hzB, a, haA, haz⟩, hxa.trans haz⟩

/-- The same refinement preserves cone density when B is globally
dense at the support level of A. -/
theorem refineOver_denseAbove_of_denseAt
    {A B : HeterogeneousMatrix P}
    {base : Fin d → U} {k l : ℕ}
    (hAlevel : A.OnLevel l)
    (hA : A.DenseAbove base k)
    (hB : B.DenseAt l) :
    (A.refineOver B).DenseAbove base k := by
  intro i x hx hbasex
  obtain ⟨a, haA, hxa⟩ := hA i x hx hbasex
  obtain ⟨z, hzB, haz⟩ :=
    hB i a (hAlevel i a haA)
  exact ⟨z, ⟨hzB, a, haA, haz⟩, hxa.trans haz⟩

/-- Refining a level-supported matrix by the complete same
source level leaves its *product carrier* unchanged. -/
theorem refineOver_fullLevel_carrier
    (A : HeterogeneousMatrix P) {l : ℕ}
    (hA : A.OnLevel l) :
    (A.refineOver (fullLevel P l)).carrier = A.carrier := by
  ext z
  constructor
  · intro hz i
    obtain ⟨hzLevel, a, ha, haz⟩ := hz i
    have hRank : U.level a = U.level (z i) := by
      calc
        U.level a = (P i).levels l := (hA i a ha).2
        _ = U.level (z i) := hzLevel.2.symm
    have hEq : a = z i :=
      U.eq_of_le_of_level_eq haz hRank
    simpa only [hEq] using ha
  · intro hz i
    exact ⟨hA i (z i) (hz i), z i, hz i, le_rfl⟩

end HeterogeneousMatrix
end GeneralTree
end Milliken
