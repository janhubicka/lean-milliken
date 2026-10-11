import Milliken.GeneralTree.Ancestry
import Milliken.GeneralTree.MaxLevel
import Milliken.GeneralTree.OrderLemmas

/-!
# Confinement of refinements with a protected finite strong-tree stem

A.3(2) requires a strong tree C which keeps the prescribed initial
levels of B but which, inside the descendant cones of the *used* a-frontier,
only uses nodes of a chosen refinement X. Other B-frontier cones
must remain available for a strong continuation.

Once such C has been constructed, the neighborhood-inclusion
conclusion is independent of how it was built. Any strong refinement
Y of C with the same finite stem as X is forced to lie in X:
its nodes on or below the stem's last selected level lie in the
common finite approximation; every later node belongs to one of the used frontier cones
and hence lies in X.

This file proves the complete confinement argument for arbitrary
locally finite pruned rooted trees. Constructing the protected
C itself remains the genuine outstanding A.3(2) problem.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Agreement of a nonempty finite strong stem determines the
ambient rank of its last selected source level. -/
theorem selectedLastLevel_eq_of_r_succ_eq
    (X Y : SInfinity U) (n : ℕ)
    (h : r (n + 1) Y = r (n + 1) X) :
    Y.levels n = X.levels n := by
  obtain ⟨x, hxY⟩ := Y.sourceLevel_nonempty n
  have hxMax : x ∈ maxLevel (r (n + 1) Y) := by
    rw [maxLevel_r_succ]
    exact hxY
  have hxMaxX : x ∈ maxLevel (r (n + 1) X) := by
    rw [← h]
    exact hxMax
  have hxX : x ∈ X.sourceLevel n := by
    rwa [maxLevel_r_succ] at hxMaxX
  exact hxY.2.symm.trans hxX.2

/-- The relative protected-cone confinement lemma:
if Y refines C and has X's first n+1 source levels, and C uses
only X-nodes **inside the descendant cones of X's n-th frontier**,
then Y is a strong refinement of X. Unused C-frontier cones may
be continued freely outside X: this is essential for A.3(2). -/
theorem refines_of_protected_tail
    (X C Y : SInfinity U) (n : ℕ)
    (hYC : Y.Refines C)
    (hYstem : r (n + 1) Y = r (n + 1) X)
    (hCtail : ∀ z ∈ C.carrier,
      (∃ x ∈ X.sourceLevel n, x ≤ z) → z ∈ X.carrier) :
    Y.Refines X := by
  have hsource : Y.sourceLevel n = X.sourceLevel n := by
    calc
      Y.sourceLevel n = maxLevel (r (n + 1) Y) :=
        (maxLevel_r_succ Y n).symm
      _ = maxLevel (r (n + 1) X) := by rw [hYstem]
      _ = X.sourceLevel n := maxLevel_r_succ X n
  intro z hzY
  obtain ⟨k, hzk⟩ := Y.carrier_levels z hzY
  by_cases hkn : k ≤ n
  · have hzPrefixY : z ∈ Y.initialPart (n + 1) :=
      ⟨hzY, k, Nat.lt_succ_of_le hkn, hzk⟩
    have hprefixEq : Y.initialPart (n + 1) =
        X.initialPart (n + 1) :=
      congrArg FiniteApprox.carrier hYstem
    have hzPrefixX : z ∈ X.initialPart (n + 1) := by
      rw [← hprefixEq]
      exact hzPrefixY
    exact X.initialPart_subset (n + 1) hzPrefixX
  · have hnk : n ≤ k := by omega
    obtain ⟨x, hx, hxz⟩ :=
      Y.exists_sourceLevel_ancestor hnk
        (show z ∈ Y.sourceLevel k from ⟨hzY, hzk⟩)
    have hxX : x ∈ X.sourceLevel n := by
      rw [← hsource]
      exact hx
    exact hCtail z (hYC hzY) ⟨x, hxX, hxz⟩

/-- The A.3(2) neighborhood inclusion follows when a protected C
agrees with B's required prefix and **only the used a-frontier
cones** are confined to X. Other frontier cones may remain in B. -/
theorem basicNeighborhood_subset_of_protected_tail
    (X C : SInfinity U) (n : ℕ)
    (hCtail : ∀ z ∈ C.carrier,
      (∃ x ∈ X.sourceLevel n, x ≤ z) → z ∈ X.carrier) :
    BasicNeighborhood (r (n + 1) X) C ⊆
      BasicNeighborhood (r (n + 1) X) X := by
  intro Y hY
  refine ⟨refines_of_protected_tail X C Y n hY.1 hY.2 hCtail,
    hY.2⟩

end GeneralTree
end Milliken
