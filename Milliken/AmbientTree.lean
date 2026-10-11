import Mathlib

/-!
# Ambient finitely branching rooted trees

Todorčević's Chapter 6 fixes a rooted finitely branching tree of height
`ω` with no terminal nodes.  Mathlib's `RootedTree` already supplies the
order-theoretic rooted-tree structure; this wrapper adds exactly the two
hypotheses used in the Milliken space: finite branching and absence of
terminal nodes.

The homogeneous tree `List ι` used by the Halpern--Läuchli development is
kept as the computational core for now.  This file is the target-neutral
interface used by the final Chapter 6 Ramsey-space construction.
-/

namespace Milliken

/-- A rooted finitely branching tree with no terminal nodes.  The no-terminal
condition forces arbitrarily large finite height because predecessor chains
in a `RootedTree` are finite. -/
structure AmbientTree where
  toRootedTree : RootedTree
  finite_children :
    ∀ x : toRootedTree, ({y : toRootedTree | x ⋖ y} : Set toRootedTree).Finite
  has_child :
    ∀ x : toRootedTree, ∃ y : toRootedTree, x ⋖ y

namespace AmbientTree

instance : CoeSort AmbientTree Type :=
  ⟨fun U => U.toRootedTree.α⟩

instance (U : AmbientTree) : SemilatticeInf U :=
  U.toRootedTree.semilatticeInf

instance (U : AmbientTree) : OrderBot U :=
  U.toRootedTree.orderBot

instance (U : AmbientTree) : PredOrder U :=
  U.toRootedTree.predOrder

instance (U : AmbientTree) : IsPredArchimedean U :=
  U.toRootedTree.isPredArchimedean

/-- Immediate successors of a node. -/
def children (U : AmbientTree) (x : U) : Set U :=
  {y | x ⋖ y}

theorem children_finite (U : AmbientTree) (x : U) :
    (U.children x).Finite :=
  U.finite_children x

theorem children_nonempty (U : AmbientTree) (x : U) :
    (U.children x).Nonempty := by
  rcases U.has_child x with ⟨y, hy⟩
  exact ⟨y, hy⟩

/-- Height of a node above the root, defined as the least number of
predecessor steps needed to reach the root. -/
noncomputable def level (U : AmbientTree) (x : U) : ℕ := by
  classical
  exact Nat.find ((show (⊥ : U) ≤ x from bot_le).exists_pred_iterate)

theorem pred_iterate_level (U : AmbientTree) (x : U) :
    (Order.pred^[U.level x]) x = (⊥ : U) := by
  classical
  exact Nat.find_spec ((show (⊥ : U) ≤ x from bot_le).exists_pred_iterate)

theorem level_minimal (U : AmbientTree) (x : U) {n : ℕ}
    (hn : (Order.pred^[n]) x = (⊥ : U)) :
    U.level x ≤ n := by
  classical
  exact Nat.find_min' ((show (⊥ : U) ≤ x from bot_le).exists_pred_iterate) hn

@[simp] theorem level_root (U : AmbientTree) :
    U.level (⊥ : U) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact level_minimal U (⊥ : U) (by simp)

/-- The `n`th level of an ambient tree. -/
def levelSet (U : AmbientTree) (n : ℕ) : Set U :=
  {x | U.level x = n}

/-- Ambient rank is monotone along the ancestor order.  This elementary
lemma is crucial for source-level and finite-strong-subtree arguments. -/
theorem level_mono (U : AmbientTree) {x y : U} (hxy : x ≤ y) :
    U.level x ≤ U.level y := by
  have hiter :
      ∀ k : ℕ, (Order.pred^[k]) x ≤ (Order.pred^[k]) y := by
    intro k
    induction k with
    | zero =>
        simpa only [Function.iterate_zero_apply] using hxy
    | succ k ih =>
        simp only [Function.iterate_succ_apply']
        exact Order.pred_mono ih
  apply U.level_minimal x
  have hx := hiter (U.level y)
  rw [U.pred_iterate_level y] at hx
  exact le_antisymm hx bot_le

/-- The ambient height increases by exactly one along an immediate
successor. No assumption of globally bounded branching is used. -/
theorem level_covBy (U : AmbientTree) {x y : U}
    (hxy : x ⋖ y) :
    U.level y = U.level x + 1 := by
  have hpred : Order.pred y = x :=
    Order.pred_eq_of_covBy hxy
  have hbot_lt : (⊥ : U) < y :=
    lt_of_le_of_lt bot_le hxy.lt
  have hyne : y ≠ (⊥ : U) := ne_of_gt hbot_lt
  have hypos : 0 < U.level y := by
    by_contra hn
    have hz : U.level y = 0 := by omega
    have hybot : y = (⊥ : U) := by
      simpa [hz] using (U.pred_iterate_level y)
    exact hyne hybot
  have hyn : U.level y = (U.level y - 1) + 1 := by omega
  have hxiter :
      (Order.pred^[U.level y - 1]) x = (⊥ : U) := by
    calc
      (Order.pred^[U.level y - 1]) x =
          (Order.pred^[(U.level y - 1) + 1]) y := by
            rw [Function.iterate_succ_apply, hpred]
      _ = (⊥ : U) := by
            rw [← hyn]
            exact U.pred_iterate_level y
  have hyiter :
      (Order.pred^[U.level x + 1]) y = (⊥ : U) := by
    rw [Function.iterate_succ_apply, hpred]
    exact U.pred_iterate_level x
  have hxle := U.level_minimal x hxiter
  have hyle := U.level_minimal y hyiter
  omega

/-- Ambient levels are strictly increasing along proper ancestor
relations. -/
theorem level_lt (U : AmbientTree) {x y : U}
    (hxy : x < y) : U.level x < U.level y := by
  have hpred : x ≤ Order.pred y := Order.le_pred_of_lt hxy
  have hyne : y ≠ (⊥ : U) := by
    intro hy
    have hbot : x < (⊥ : U) := by simpa [hy] using hxy
    exact (not_lt_of_ge bot_le) hbot
  have hcov : Order.pred y ⋖ y :=
    Order.pred_covBy_of_not_isMin
      ((not_isMin_iff_ne_bot).mpr hyne)
  have hle := U.level_mono hpred
  have hstep := U.level_covBy hcov
  omega

/-- Ancestor comparison together with equal ambient levels forces
equality. -/
theorem eq_of_le_of_level_eq (U : AmbientTree) {x y : U}
    (hxy : x ≤ y)
    (hlevels : U.level x = U.level y) : x = y := by
  rcases hxy.eq_or_lt with heq | hlt
  · exact heq
  · have hlevels_lt := U.level_lt hlt
    omega

end AmbientTree

end Milliken
