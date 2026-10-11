import Milliken.GeneralTree.OrderRealization
import Milliken.GeneralTree.ApproximationSystem
import RamseySpace.Finitization

/-!
# Todorčević A.2(3) for the literal finite order (6.3)

When a realised finite strong stem a is an initial part of b, and
b is below c in the published finitization, choose a node from
the last source level of a. Its ambient rank identifies a unique
selected level j in a realizer of c. This selected level determines
the required shorter approximation d = r_(j+1)(C).

All nodes of a then occur in d, and the maximal selected level
of a is included in the maximal level of d, giving precisely the
book's relation (6.3), not merely carrier inclusion.

Together with the previously checked lower-finiteness and order
realization clauses this packages a complete A.2 instance for
arbitrary pruned locally finite ambient trees, with no fixed
alphabet or global branching degree bound.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- A.2(3): initial-segment compatibility with the published
maximal-level finitization (6.3). -/
theorem bookLeFin_prefix_compatible
    {n m k : ℕ}
    {a : SFinite U n} {b : SFinite U m}
    {c : SFinite U k}
    (hab : (generalApproximationSystem U).IsInitial a b)
    (hbc : bookLeFin ⟨m, b⟩ ⟨k, c⟩) :
    ∃ (j : ℕ) (d : SFinite U j),
      (generalApproximationSystem U).IsInitial d c ∧
      bookLeFin ⟨n, a⟩ ⟨j, d⟩ := by
  obtain ⟨hnm, W, hWa, hWb⟩ := hab
  obtain ⟨C, hC⟩ := c.realised
  have hCeq : r k C = c := by
    apply FiniteApprox.ext_carrier
    exact hC.symm
  have hbcsub : b.carrier ⊆ c.carrier :=
    (bookLeFin_iff.mp hbc).1
  cases n with
  | zero =>
      refine ⟨0, r 0 C, ⟨Nat.zero_le k, C, rfl, hCeq⟩, ?_⟩
      rw [← hWa]
      exact bookLeFin_zero_left W ⟨0, r 0 C⟩
  | succ n =>
      obtain ⟨x, hx⟩ := W.sourceLevel_nonempty n
      have hxB : x ∈ b.carrier := by
        rw [← hWb]
        exact W.sourceLevel_subset_initialPart
          (by omega : n < m) hx
      have hxC : x ∈ C.initialPart k := by
        rw [← hC]
        exact hbcsub hxB
      obtain ⟨_, j, hjk, hxlevel⟩ := hxC
      have hmatch : W.levels n = C.levels j :=
        hx.2.symm.trans hxlevel
      refine ⟨j + 1, r (j + 1) C,
        ⟨Nat.succ_le_of_lt hjk, C, rfl, hCeq⟩, ?_⟩
      rw [← hWa]
      apply bookLeFin_iff.mpr
      constructor
      · change W.initialPart (n + 1) ⊆ C.initialPart (j + 1)
        rintro y ⟨hyW, l, hln, hylevel⟩
        have hyB : y ∈ b.carrier := by
          rw [← hWb]
          exact W.initialPart_mono hnm
            ⟨hyW, l, hln, hylevel⟩
        have hyC : y ∈ C.carrier := by
          apply C.initialPart_subset k
          rw [← hC]
          exact hbcsub hyB
        have hyle : U.level y ≤ C.levels j := by
          calc
            U.level y = W.levels l := hylevel
            _ ≤ W.levels n :=
              W.levels_strictMono.monotone (Nat.le_of_lt_succ hln)
            _ = C.levels j := hmatch
        exact C.mem_initialPart_of_level_le j hyC hyle
      · change maxLevel (r (n + 1) W) ⊆
          maxLevel (r (j + 1) C)
        rw [maxLevel_r_succ W n, maxLevel_r_succ C j]
        rintro y ⟨hyW, hylevel⟩
        have hyB : y ∈ b.carrier := by
          rw [← hWb]
          exact W.sourceLevel_subset_initialPart
            (by omega : n < m) ⟨hyW, hylevel⟩
        have hyC : y ∈ C.carrier := by
          apply C.initialPart_subset k
          rw [← hC]
          exact hbcsub hyB
        exact ⟨hyC, hylevel.trans hmatch⟩

/-- Todorčević A.2, proved with the *literal* book finite order (6.3)
for arbitrary pruned, locally finitely branching rooted ambient trees. -/
def generalBookFinitization (U : AmbientTree) :
    RamseySpace.Finitization (generalApproximationSystem U) where
  leFin := bookLeFin
  leFin_refl := by
    intro a
    exact bookLeFin_refl a
  leFin_trans := by
    intro a b c hab hbc
    exact bookLeFin_trans hab hbc
  lowerFinite := by
    intro b
    exact bookLeFin_lowerFinite b
  realizesOrder := by
    intro S T
    exact refines_iff_forall_bookLeFin_r S T
  prefix_leFin := by
    intro n m k a b c hab hbc
    exact bookLeFin_prefix_compatible hab hbc

end GeneralTree
end Milliken
