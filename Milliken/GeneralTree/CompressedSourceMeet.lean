import Milliken.GeneralTree.CompressedSourcePred

/-!
# Greatest common selected-source ancestors in the compressed tree

The compressed order is a rooted tree, even when the original strong
tree skips arbitrarily large source-level intervals. Two compressed
nodes have a unique selected ancestor of every earlier rank; their
greatest common ancestor is found by maximizing the finite set of
ranks at which those canonical ancestors coincide.

This produces a genuine Mathlib SemilatticeInf instance on the
*full* compressed-node set. No branches are discarded at skipped
levels, and node-dependent finite branching remains unrestricted.

Together with CompressedSourcePred, this supplies the four
order structures used by RootedTree: PartialOrder, OrderBot,
PredOrder, and IsPredArchimedean, as well as SemilatticeInf.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace CompressedSourceSelection

variable (S : StrongSubtree U) (f : CompressedSourceSelection)

/-- Selected compressed rank zero contains only the root. -/
theorem node_eq_bot_of_index_zero
    (x : Node S f) (h0 : x.1 = 0) :
    x = (⊥ : Node S f) := by
  have hb : (⊥ : Node S f) ≤ x := bot_le
  have hindex : (⊥ : Node S f).1 = x.1 := by
    rw [h0]
    rfl
  exact (node_eq_of_le_index_eq S f hb hindex).symm

/-- Two nodes have a common ancestor at selected index k when
their canonical truncations to that index coincide. -/
def CommonRank (x y : Node S f) (k : ℕ) : Prop :=
  ∃ (hx : k ≤ x.1) (hy : k ≤ y.1),
    nodeAncestor S f hx x rfl =
      nodeAncestor S f hy y rfl

/-- Every pair shares the source-zero root. -/
theorem commonRank_zero (x y : Node S f) :
    CommonRank S f x y 0 := by
  refine ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩
  have hx :
      nodeAncestor S f (Nat.zero_le _) x rfl =
        (⊥ : Node S f) :=
    node_eq_bot_of_index_zero S f _ rfl
  have hy :
      nodeAncestor S f (Nat.zero_le _) y rfl =
        (⊥ : Node S f) :=
    node_eq_bot_of_index_zero S f _ rfl
  exact hx.trans hy.symm

/-- The largest common selected-source ancestor rank. -/
noncomputable def commonIndex (x y : Node S f) : ℕ := by
  classical
  exact Nat.findGreatest
    (CommonRank S f x y) (min x.1 y.1)

theorem commonIndex_le_left (x y : Node S f) :
    commonIndex S f x y ≤ x.1 := by
  classical
  exact (Nat.findGreatest_le (P := CommonRank S f x y) _).trans (min_le_left _ _)

theorem commonIndex_le_right (x y : Node S f) :
    commonIndex S f x y ≤ y.1 := by
  classical
  exact (Nat.findGreatest_le (P := CommonRank S f x y) _).trans (min_le_right _ _)

theorem commonIndex_spec (x y : Node S f) :
    CommonRank S f x y (commonIndex S f x y) := by
  classical
  exact Nat.findGreatest_spec
    (P := CommonRank S f x y) (Nat.zero_le _)
    (commonRank_zero S f x y)

/-- The compressed meet is the actual common ancestor of
maximal compressed index. -/
noncomputable def compressedInf (x y : Node S f) : Node S f :=
  nodeAncestor S f (commonIndex_le_left S f x y) x rfl

theorem compressedInf_le_left (x y : Node S f) :
    compressedInf S f x y ≤ x :=
  nodeAncestor_le S f (commonIndex_le_left S f x y) x rfl

theorem compressedInf_le_right (x y : Node S f) :
    compressedInf S f x y ≤ y := by
  obtain ⟨hx, hy, heq⟩ := commonIndex_spec S f x y
  have hInf :
      compressedInf S f x y =
        nodeAncestor S f hx x rfl := rfl
  rw [hInf, heq]
  exact nodeAncestor_le S f hy y rfl

/-- Every common ancestor is below the maximal common ancestor:
the key semilattice meet property. -/
theorem le_compressedInf
    (x y z : Node S f)
    (hzx : z ≤ x) (hzy : z ≤ y) :
    z ≤ compressedInf S f x y := by
  have hzxrank : z.1 ≤ x.1 := nodeIndex_mono S f hzx
  have hzyrank : z.1 ≤ y.1 := nodeIndex_mono S f hzy
  have hboth : CommonRank S f x y z.1 := by
    refine ⟨hzxrank, hzyrank, ?_⟩
    have hx :
        z = nodeAncestor S f hzxrank x rfl :=
      nodeAncestor_unique S f hzxrank x rfl z rfl hzx
    have hy :
        z = nodeAncestor S f hzyrank y rfl :=
      nodeAncestor_unique S f hzyrank y rfl z rfl hzy
    exact hx.symm.trans hy
  have hmax :
      z.1 ≤ commonIndex S f x y := by
    classical
    exact Nat.le_findGreatest
      (P := CommonRank S f x y)
      (le_min hzxrank hzyrank) hboth
  exact node_le_ancestor_of_index_le S f x z hzx
    (commonIndex_le_left S f x y) hmax

/-- The full compressed ancestor order has an actual greatest
common ancestor in the sense of Mathlib's SemilatticeInf. -/
noncomputable instance nodeSemilatticeInf :
    SemilatticeInf (Node S f) where
  inf := compressedInf S f
  inf_le_left := compressedInf_le_left S f
  inf_le_right := compressedInf_le_right S f
  le_inf := by
    intro z x y hzx hzy
    exact le_compressedInf S f x y z hzx hzy

end CompressedSourceSelection
end GeneralTree
end Milliken
