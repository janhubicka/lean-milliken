import Milliken.GeneralTree.CompressedSourceMeet

/-!
# The full selected-level compression is a fresh AmbientTree

The full compressed nodes are all actual nodes at S.sourceLevel (f n).
The compressed order is original ancestry, its meet is the greatest
common retained selected ancestor, and its parent jumps from rank n+1
to rank n. Both are proved independently of any Ramsey theorem.

We now show that immediate compressed children are **all** nodes
on the next selected source level extending the parent. This gives
finite but potentially unbounded node-dependent degrees and no
terminal nodes, so the compressed order is a genuine Mathlib
RootedTree and therefore an AmbientTree.

The difference from strong thinning is fundamental: the new
ambient tree retains the entire full selected frontier, which is
the geometric operation required by Todorčević Remark 3.8.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace CompressedSourceSelection

variable (S : StrongSubtree U) (f : CompressedSourceSelection)

/-- A cover in the compressed ancestor order advances the selected
source index by exactly one, regardless of the old ambient gap. -/
theorem node_covBy_iff (a b : Node S f) :
    a ⋖ b ↔ a ≤ b ∧ b.1 = a.1 + 1 := by
  constructor
  · intro hab
    have hidx : a.1 < b.1 :=
      nodeIndex_lt_of_lt S f hab.lt
    have hnext : b.1 ≤ a.1 + 1 := by
      by_contra hnot
      have hstep : a.1 + 1 ≤ b.1 := by omega
      let c : Node S f :=
        nodeAncestor S f hstep b rfl
      have hac : a ≤ c :=
        node_le_ancestor_of_index_le S f b a hab.le
          hstep (Nat.le_succ _)
      have hcb : c ≤ b :=
        nodeAncestor_le S f hstep b rfl
      have halt : a < c := by
        apply lt_of_le_of_ne hac
        intro heq
        have heqi := congrArg (fun z : Node S f => z.1) heq
        have hcindex : c.1 = a.1 + 1 :=
          nodeAncestor_index S f hstep b rfl
        omega
      have hclt : c < b := by
        apply lt_of_le_of_ne hcb
        intro heq
        have heqi := congrArg (fun z : Node S f => z.1) heq
        have hcindex : c.1 = a.1 + 1 :=
          nodeAncestor_index S f hstep b rfl
        omega
      exact hab.2 halt hclt
    exact ⟨hab.le, by omega⟩
  · rintro ⟨hab, hrank⟩
    have hlt : a < b := by
      apply lt_of_le_of_ne hab
      intro heq
      have h := congrArg (fun z : Node S f => z.1) heq
      omega
    refine ⟨hlt, ?_⟩
    intro z haz hzb
    have ha := nodeIndex_lt_of_lt S f haz
    have hb := nodeIndex_lt_of_lt S f hzb
    omega

/-- Every compressed node has finitely many immediate descendants:
they belong to its next *full* finite selected-source frontier. -/
theorem node_children_finite (a : Node S f) :
    ({b : Node S f | a ⋖ b} : Set (Node S f)).Finite := by
  apply (node_level_finite S f (a.1 + 1)).subset
  intro b hb
  exact (node_covBy_iff S f a b).mp hb |>.2

/-- Every compressed node has a child, with the actual
next-full-frontier descendant supplied by the original strong tree. -/
theorem node_has_child (a : Node S f) :
    ∃ b : Node S f, a ⋖ b := by
  obtain ⟨z⟩ := child_nonempty S f a.2
  let b : Node S f := ⟨a.1 + 1, z.1⟩
  have hab : a ≤ b :=
    (node_le_iff S f a b).mpr z.2
  exact ⟨b, (node_covBy_iff S f a b).mpr ⟨hab, rfl⟩⟩

/-- The full source compression as a genuinely new rooted tree,
rather than a strong subtree in the original ambient order. -/
noncomputable def compressedRootedTree : RootedTree where
  α := Node S f

/-- Actual finite, unbounded-degree full selected-level compression.
The AmbientTree axioms are consequences of the proved node geometry,
not of any Halpern–Läuchli or Ramsey theorem. -/
noncomputable def compressedAmbientTree : AmbientTree where
  toRootedTree := compressedRootedTree S f
  finite_children := by
    intro a
    exact node_children_finite S f a
  has_child := by
    intro a
    exact node_has_child S f a

end CompressedSourceSelection
end GeneralTree
end Milliken
