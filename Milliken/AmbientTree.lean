import Mathlib.Order.SuccPred.Tree

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
    ∀ x : toRootedTree, {y : toRootedTree | x ⋖ y}.Finite
  has_child :
    ∀ x : toRootedTree, ∃ y : toRootedTree, x ⋖ y

namespace AmbientTree

instance : CoeSort AmbientTree Type* :=
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
noncomputable def level (U : AmbientTree) (x : U) : ℕ :=
  Nat.find (bot_le (a := x)).exists_pred_iterate

theorem pred_iterate_level (U : AmbientTree) (x : U) :
    (Order.pred^[U.level x]) x = (⊥ : U) :=
  Nat.find_spec (bot_le (a := x)).exists_pred_iterate

theorem level_minimal (U : AmbientTree) (x : U) {n : ℕ}
    (hn : (Order.pred^[n]) x = (⊥ : U)) :
    U.level x ≤ n :=
  Nat.find_min' (bot_le (a := x)).exists_pred_iterate hn

@[simp] theorem level_root (U : AmbientTree) :
    U.level (⊥ : U) = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply U.level_minimal
  simp

/-- The `n`th level of an ambient tree. -/
def levelSet (U : AmbientTree) (n : ℕ) : Set U :=
  {x | U.level x = n}

end AmbientTree

end Milliken
