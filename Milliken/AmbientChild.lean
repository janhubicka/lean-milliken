import Milliken.AmbientTree

/-!
# Immediate child on a branch of a rooted tree

If x is a proper ancestor of z, there is an immediate ambient successor
y of x below z. The proof follows the parent of z downwards, inducting
on its finite ambient rank. No finite alphabet, homogeneous branching
or degree bound is needed.

This permits us to prove that a strong subtree contains the complete
next selected source level when it retains the preceding complete
source level. This is the prefix-preserving thinning step needed
in Todorčević A.3(2).
-/

namespace Milliken
namespace AmbientTree

/-- The first ambient successor on the branch from x to any proper
descendant z exists and remains below z. -/
theorem exists_child_le_of_lt (U : AmbientTree)
    {x z : U} (hx : x < z) :
    ∃ y : U, x ⋖ y ∧ y ≤ z := by
  have aux :
      ∀ N : ℕ, ∀ (a b : U),
        U.level b = N → a < b →
          ∃ y : U, a ⋖ y ∧ y ≤ b := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro a b hb hab
        have hbne : b ≠ (⊥ : U) := by
          intro hbot
          have hbad : a < (⊥ : U) := by
            simpa only [hbot] using hab
          exact (not_lt_of_ge bot_le) hbad
        have hpb : Order.pred b ⋖ b :=
          Order.pred_covBy_of_not_isMin
            ((not_isMin_iff_ne_bot).mpr hbne)
        have hap : a ≤ Order.pred b :=
          Order.le_pred_of_lt hab
        rcases hap.eq_or_lt with heq | hlt
        · refine ⟨b, ?_, le_rfl⟩
          simpa only [heq] using hpb
        · have hrank : U.level (Order.pred b) < N := by
            have hstep := U.level_covBy hpb
            omega
          obtain ⟨y, hay, hyp⟩ :=
            ih (U.level (Order.pred b)) hrank
              a (Order.pred b) rfl hlt
          exact ⟨y, hay, hyp.trans hpb.le⟩
  exact aux (U.level z) x z rfl hx

/-- Immediate children of the same parent with a common descendant
are equal. -/
theorem children_eq_of_common_descendant
    (U : AmbientTree)
    {x y w z : U}
    (hxy : x ⋖ y) (hxw : x ⋖ w)
    (hyz : y ≤ z) (hwz : w ≤ z) :
    y = w := by
  have hlevels : U.level y = U.level w := by
    calc
      U.level y = U.level x + 1 := U.level_covBy hxy
      _ = U.level w := (U.level_covBy hxw).symm
  rcases le_total_of_directed hyz hwz with hwy | hyw
  · exact (U.eq_of_le_of_level_eq hwy hlevels.symm).symm
  · exact U.eq_of_le_of_level_eq hyw hlevels

end AmbientTree
end Milliken
