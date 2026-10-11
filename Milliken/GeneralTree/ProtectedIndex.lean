import Milliken.GeneralTree.RefinementLevels

/-!
# A common protected-prefix source-level index schedule

Suppose X refines B, and the selected source level n of X aligns
with the selected source level j of B. Construct a strictly
increasing source-index map for B that fixes every index up to j
and, beyond j, follows the source levels of X from index n.

Thus the resulting B-subtree can keep B's full depth-(j+1)
prefix while agreeing with all future ambient ranks of X.
This is precisely the global level schedule needed to combine
the used X-cones with the unused B-cones in Todorčević A.3(2).
No globally fixed branching degree is assumed.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Protect B's source levels before index j, and then follow
the indices in B of X's selected levels from index n onward. -/
noncomputable def protectedIndex
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j k : ℕ) : ℕ :=
  if k < j then k
  else X.refinementIndex B hXB (n + (k - j))

theorem protectedIndex_before
    (X B : StrongSubtree U)
    (hXB : X.Refines B)
    (n j : ℕ) {k : ℕ} (hk : k < j) :
    X.protectedIndex B hXB n j k = k := by
  simp only [protectedIndex, if_pos hk]

theorem protectedIndex_ge
    (X B : StrongSubtree U)
    (hXB : X.Refines B)
    (n j : ℕ) {k : ℕ} (hk : j ≤ k) :
    X.protectedIndex B hXB n j k =
      X.refinementIndex B hXB (n + (k - j)) := by
  simp only [protectedIndex, if_neg (not_lt.mpr hk)]

theorem protectedIndex_at_tail
    (X B : StrongSubtree U)
    (hXB : X.Refines B)
    (n j t : ℕ) :
    X.protectedIndex B hXB n j (j + t) =
      X.refinementIndex B hXB (n + t) := by
  rw [X.protectedIndex_ge B hXB n j (by omega : j ≤ j + t)]
  congr 1
  omega

/-- Alignment of one selected level determines its index in B. -/
theorem refinementIndex_eq_at_aligned_level
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j : ℕ)
    (hmatch : X.levels n = B.levels j) :
    X.refinementIndex B hXB n = j := by
  apply B.levels_strictMono.injective
  exact (X.levels_refinementIndex B hXB n).symm.trans hmatch

/-- The splice index is the identity all the way through j. -/
theorem protectedIndex_initial
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j : ℕ)
    (hmatch : X.levels n = B.levels j)
    {k : ℕ} (hk : k ≤ j) :
    X.protectedIndex B hXB n j k = k := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact X.protectedIndex_before B hXB n j hlt
  · subst k
    change X.protectedIndex B hXB n j (j + 0) = j
    rw [X.protectedIndex_at_tail B hXB n j 0]
    simpa only [Nat.add_zero] using
      X.refinementIndex_eq_at_aligned_level B hXB n j hmatch

/-- In particular the index schedule starts at the ambient root. -/
theorem protectedIndex_zero
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j : ℕ)
    (hmatch : X.levels n = B.levels j) :
    X.protectedIndex B hXB n j 0 = 0 :=
  X.protectedIndex_initial B hXB n j hmatch (Nat.zero_le j)

/-- After the protected prefix the selected ambient levels are
exactly X's future selected levels. -/
theorem protectedIndex_levels_at_tail
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j t : ℕ) :
    B.levels (X.protectedIndex B hXB n j (j + t)) =
      X.levels (n + t) := by
  rw [X.protectedIndex_at_tail B hXB n j t]
  exact (X.levels_refinementIndex B hXB (n + t)).symm

/-- The protected index schedule is strictly increasing under
the alignment of its two pieces at the cut. -/
theorem protectedIndex_strictMono
    (X B : StrongSubtree U)
    (hXB : X.Refines B) (n j : ℕ)
    (hmatch : X.levels n = B.levels j) :
    StrictMono (X.protectedIndex B hXB n j) := by
  have hj : X.refinementIndex B hXB n = j :=
    X.refinementIndex_eq_at_aligned_level B hXB n j hmatch
  apply strictMono_nat_of_lt_succ
  intro k
  by_cases hsmall : k + 1 < j
  · have hk : k < j := by omega
    rw [X.protectedIndex_before B hXB n j hk,
        X.protectedIndex_before B hXB n j hsmall]
    omega
  · by_cases hk : k < j
    · have hkEq : k + 1 = j := by omega
      rw [X.protectedIndex_before B hXB n j hk,
          X.protectedIndex_ge B hXB n j
            (show j ≤ k + 1 by omega)]
      have harg : n + (k + 1 - j) = n := by omega
      rw [harg, hj]
      omega
    · have hkge : j ≤ k := by omega
      rw [X.protectedIndex_ge B hXB n j hkge,
          X.protectedIndex_ge B hXB n j
            (show j ≤ k + 1 by omega)]
      exact X.refinementIndex_strictMono B hXB (by omega)

end StrongSubtree
end GeneralTree
end Milliken
