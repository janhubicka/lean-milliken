import Milliken.GeneralTree.HeterogeneousRestrictedReduction
import Milliken.GeneralTree.HeterogeneousHDHLBase

/-!
# Product density and the unary case of restricted HDHL

Absence of a complementary matrix dense between two selected
source levels is a stronger hypothesis than absence of a
*particular* bad cone. Given a failed product-density test at
the first selected positive level, keep the entire cone above
its witness tuple: this is a complementary matrix dense at
the next selected level, contradicting the reduced assumption.

For one coordinate, product density itself gives a dense
matrix by projection. Thus the selected-level reduced theorem
has an unconditional one-dimensional base case, for arbitrary
finitely branching strong trees and arbitrary strictly
increasing selected-source-index sequences.

The higher-dimensional step needs the heterogeneous reduced
induction over the tree compressed to these selected levels.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The complete retained carrier of an arbitrary heterogeneous
product is a matrix dense at every selected source index. -/
def heterogeneousFullCarrier (P : Fin d → StrongSubtree U) :
    HeterogeneousMatrix P where
  coord := fun i => (P i).carrier
  coord_sub := fun i z hz => hz

theorem heterogeneousFullCarrier_denseAt
    (P : Fin d → StrongSubtree U) (n : ℕ) :
    (heterogeneousFullCarrier P).DenseAt n := by
  intro i z hz
  exact ⟨z, hz.1, le_rfl⟩

/-- A restricted no-complement-somewhere-dense hypothesis implies
product density in Q on the first selected positive source level.
The witnesses can be taken inside the retained product carrier. -/
theorem heterogeneousProductDense_of_noRestrictedComplement
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (Q : Set (Fin d → U))
    (hno :
      ¬ HeterogeneousContainsRestrictedSomewhereDense
        P levels Qᶜ) :
    HeterogeneousProductDenseAt P
      (Q ∩ (heterogeneousFullCarrier P).carrier) (levels 1) := by
  classical
  intro base
  by_contra hfail
  let Full := heterogeneousFullCarrier P
  let Bad : HeterogeneousMatrix P := Full.restrictAbove base.1
  have hFull : Full.DenseAt (levels 2) :=
    heterogeneousFullCarrier_denseAt P (levels 2)
  have hBadDense : Bad.DenseAbove base.1 (levels 2) :=
    Full.restrictAbove_denseAbove base.1 (levels 2) hFull
  have hBadSubset : Bad.carrier ⊆ Qᶜ := by
    intro x hx hQ
    have hxFull : x ∈ Full.carrier :=
      Full.restrictAbove_carrier_subset base.1 hx
    have hbx : ∀ i, base.1 i ≤ x i := by
      intro i
      exact (hx i).2
    apply hfail
    exact ⟨x, ⟨hQ, hxFull⟩, hbx⟩
  apply hno
  exact ⟨Bad, ⟨1, 2, by omega, base, hBadDense⟩,
    hBadSubset⟩

/-- The dimension-one selected-level restricted reduced theorem,
unconditionally and with no homogeneous branching assumption. -/
theorem heterogeneousRestrictedReduced_one
    (P : Fin 1 → StrongSubtree U)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels) :
    HeterogeneousRestrictedReducedDichotomy P levels := by
  intro Q hno
  let Full : HeterogeneousMatrix P :=
    heterogeneousFullCarrier P
  have hProduct :
      HeterogeneousProductDenseAt P
        (Q ∩ Full.carrier) (levels 1) :=
    heterogeneousProductDense_of_noRestrictedComplement
      P levels hlevels Q hno
  let N : HeterogeneousMatrix P :=
    heterogeneousUnaryProjection P Full
      (Q ∩ Full.carrier) Set.inter_subset_right
  refine ⟨N, ?_, ?_⟩
  · exact heterogeneousUnaryProjection_dense P Full
      (Q ∩ Full.carrier) Set.inter_subset_right hProduct
  · exact
      (heterogeneousUnaryProjection_carrier_subset
        P Full (Q ∩ Full.carrier) Set.inter_subset_right).trans
      Set.inter_subset_left

end GeneralTree
end Milliken
