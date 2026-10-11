import Milliken.GeneralTree.LevelPathCoding

/-!
# Surjectivity of the rank-varying path interpretation

Every ambient descendant of x is reached by a coded natural-number
word. The proof follows its finite predecessor chain and chooses an
abstract label for each edge, without a global bound on branching.

This proves a *surjective* tree-word presentation, not a regular-tree
strong embedding or heterogeneous Halpern--Läuchli.
-/

namespace Milliken
namespace GeneralTree

theorem le_evalPath (U : AmbientTree) (x : U) (as : List ℕ) :
    x ≤ evalPath U x as := by
  induction as generalizing x with
  | nil => exact le_rfl
  | cons a as ih =>
      exact (childFromLabel_covBy U x a).le.trans
        (ih (childFromLabel U x a))

theorem exists_evalPath_of_le
    (U : AmbientTree) {x z : U} (hx : x ≤ z) :
    ∃ as : List ℕ, evalPath U x as = z := by
  have aux :
      ∀ N : ℕ, ∀ z : U, U.level z = N →
        ∀ x : U, x ≤ z →
          ∃ as : List ℕ, evalPath U x as = z := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro z hzN x hxz
        rcases hxz.eq_or_lt with heq | hlt
        · subst z
          exact ⟨[], rfl⟩
        · have hznot : z ≠ (⊥ : U) := by
            intro hzroot
            have hbad : x < (⊥ : U) := by
              simpa only [hzroot] using hlt
            exact (not_lt_of_ge bot_le) hbad
          have hcov : Order.pred z ⋖ z :=
            Order.pred_covBy_of_not_isMin
              ((not_isMin_iff_ne_bot).mpr hznot)
          have hxpred : x ≤ Order.pred z :=
            Order.le_pred_of_lt hlt
          have hlevelpred : U.level (Order.pred z) < N := by
            have hh := U.level_covBy hcov
            omega
          obtain ⟨as, has⟩ :=
            ih (U.level (Order.pred z)) hlevelpred
              (Order.pred z) rfl x hxpred
          obtain ⟨a, ha⟩ := exists_childFromLabel U hcov
          refine ⟨as ++ [a], ?_⟩
          rw [evalPath_append, has]
          change childFromLabel U (Order.pred z) a = z
          exact ha
  exact aux (U.level z) z rfl x hx

theorem evalPath_length_of_eq (U : AmbientTree)
    {x z : U} {as : List ℕ}
    (h : evalPath U x as = z) :
    as.length = U.level z - U.level x := by
  have hh := evalPath_level U x as
  rw [h] at hh
  omega

end GeneralTree
end Milliken
