import Milliken.GeneralTree.CompressedSourceOrder

/-!
# Parents and finite ancestor chains in the full compressed tree

The parent of a node on selected source index n+1 is its unique
selected ancestor on index n. The parent of the root is the root.

We prove the predecessor is the greatest strict ancestor, so
the actual compressed node order carries the Mathlib PredOrder
structure. Every ancestor can then be reached by finitely many
parent iterations, establishing IsPredArchimedean.

This is *not* the predecessor from the old ambient tree: skipped
source levels are compressed to one step while retaining every
node on the chosen full selected frontier.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace CompressedSourceSelection

variable (S : StrongSubtree U) (f : CompressedSourceSelection)

/-- The next earlier selected-source ancestor, with the root fixed. -/
noncomputable def nodeParent : Node S f → Node S f
  | ⟨0, _⟩ => nodeRoot S f
  | ⟨n + 1, z⟩ => ⟨n, truncate S f (Nat.le_succ n) z⟩

theorem nodeParent_index (z : Node S f) :
    (nodeParent S f z).1 = z.1 - 1 := by
  rcases z with ⟨n, x⟩
  cases n with
  | zero => rfl
  | succ k => rfl

/-- The chosen compressed parent is a genuine ancestor. -/
theorem nodeParent_le (z : Node S f) :
    nodeParent S f z ≤ z := by
  rcases z with ⟨n, x⟩
  cases n with
  | zero =>
      exact bot_le
  | succ k =>
      apply (node_le_iff S f _ _).mpr
      exact truncate_below S f (Nat.le_succ k) x

/-- Ancestors of a given node are linearly ordered by their
selected-source index, even if the ambient tree has unbounded degree. -/
theorem node_le_ancestor_of_index_le
    (z x : Node S f)
    (hxz : x ≤ z)
    {m : ℕ} (hm : m ≤ z.1) (hxm : x.1 ≤ m) :
    x ≤ nodeAncestor S f hm z rfl := by
  let a : Node S f := nodeAncestor S f hm z rfl
  have haz : a ≤ z := nodeAncestor_le S f hm z rfl
  have hxU : x.2.1 ≤ z.2.1 :=
    (node_le_iff S f x z).mp hxz
  have haU : a.2.1 ≤ z.2.1 :=
    (node_le_iff S f a z).mp haz
  rcases le_total_of_directed hxU haU with hax | hxa
  · have ha_x : a ≤ x :=
      (node_le_iff S f a x).mpr hax
    have hi : m ≤ x.1 := by
      have hh := nodeIndex_mono S f ha_x
      change m ≤ x.1 at hh
      exact hh
    have heq : a.1 = x.1 := by
      change m = x.1
      omega
    have haxEq : a = x :=
      node_eq_of_le_index_eq S f ha_x heq
    exact le_of_eq haxEq.symm
  · exact (node_le_iff S f x a).mpr hxa

/-- Strict ancestry strictly increases the compressed source rank. -/
theorem nodeIndex_lt_of_lt
    {x z : Node S f} (hxz : x < z) :
    x.1 < z.1 := by
  have hle : x.1 ≤ z.1 :=
    nodeIndex_mono S f hxz.le
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · have hEq : x = z :=
      node_eq_of_le_index_eq S f hxz.le heq
    exact (hxz.ne hEq).elim

/-- No strict predecessor can lie above the immediate compressed
parent. This is the defining PredOrder property. -/
theorem node_le_parent_of_lt
    {x z : Node S f} (hxz : x < z) :
    x ≤ nodeParent S f z := by
  rcases z with ⟨n, y⟩
  cases n with
  | zero =>
      have hr := nodeIndex_lt_of_lt S f hxz
      omega
  | succ n =>
      have hr : x.1 ≤ n := by
        have hh := nodeIndex_lt_of_lt S f hxz
        omega
      exact node_le_ancestor_of_index_le S f
        (⟨n + 1, y⟩ : Node S f) x hxz.le
        (Nat.le_succ n) hr

/-- The actual full compressed tree has a genuine predecessor
operation, not the predecessor inherited from the old ambient U. -/
noncomputable instance nodePredOrder : PredOrder (Node S f) where
  pred := nodeParent S f
  pred_le := nodeParent_le S f
  min_of_le_pred := by
    intro x hx
    by_cases hzero : x.1 = 0
    · have hbot : x = (⊥ : Node S f) := by
        have hle : (⊥ : Node S f) ≤ x := bot_le
        apply node_eq_of_le_index_eq S f hle
        simpa [nodeIndex_bot S f] using hzero.symm
      subst x
      exact isMin_bot
    · have hi : x.1 ≤ (nodeParent S f x).1 :=
        nodeIndex_mono S f hx
      rw [nodeParent_index] at hi
      omega
  le_pred_of_lt := by
    intro x z hxz
    exact node_le_parent_of_lt S f hxz

/-- The recursive parent operation reaches any earlier ancestor
after finitely many steps, including when f skips arbitrarily
many source levels in the original ambient tree. -/
theorem node_exists_parent_iterate_of_le
    {x z : Node S f} (hxz : x ≤ z) :
    ∃ k : ℕ, (nodeParent S f)^[k] z = x := by
  have aux :
      ∀ (n : ℕ) (z : Node S f), z.1 = n →
        ∀ (x : Node S f), x ≤ z →
          ∃ k : ℕ, (nodeParent S f)^[k] z = x := by
    intro n
    induction n with
    | zero =>
        intro z hz x hxz
        have hindex : x.1 = z.1 := by
          have hle := nodeIndex_mono S f hxz
          omega
        have hEq : x = z :=
          node_eq_of_le_index_eq S f hxz hindex
        exact ⟨0, by simpa using hEq.symm⟩
    | succ n ih =>
        intro z hz x hxz
        by_cases heq : x = z
        · subst x
          exact ⟨0, rfl⟩
        · have hlt : x < z :=
            lt_of_le_of_ne hxz heq
          have hxp : x ≤ nodeParent S f z :=
            node_le_parent_of_lt S f hlt
          have hpindex : (nodeParent S f z).1 = n := by
            rw [nodeParent_index, hz]
            omega
          obtain ⟨k, hk⟩ :=
            ih (nodeParent S f z) hpindex x hxp
          refine ⟨k + 1, ?_⟩
          rw [Function.iterate_succ_apply']
          exact hk
  exact aux z.1 z rfl x hxz

/-- The compressed order has finite parent chains, as required
to package it into a genuinely new RootedTree. -/
noncomputable instance nodePredArchimedean :
    IsPredArchimedean (Node S f) where
  exists_pred_iterate_of_le := by
    intro x z hxz
    change ∃ k, (nodeParent S f)^[k] z = x
    exact node_exists_parent_iterate_of_le S f hxz

end CompressedSourceSelection
end GeneralTree
end Milliken
