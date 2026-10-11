import Milliken.GeneralTree.BoundaryIndex
import Milliken.GeneralTree.FiniteLevels
import Mathlib.Data.Fintype.EquivFin

/-!
# A finite alphabet at each ambient rank of an arbitrary locally finite tree

For every natural ambient level n in a rooted locally finitely branching
tree U, the level contains finitely many nodes, each with finitely many
immediate successors. Therefore a *finite but level-dependent* alphabet
can enumerate all children of every node on that level, by a surjective
map depending on the node.

The level alphabets are not assumed uniformly bounded. This is the
first structural step in transporting heterogeneous Halpern--Läuchli to
trees of words with varying finite alphabets. It does NOT reduce the
general HL theorem to the already verified fixed-alphabet Hales--Jewett:
that nonuniform combinatorial step still needs proof.
-/

namespace Milliken
namespace GeneralTree

/-- Number of uniformly available abstract labels at ambient rank n.
This is finite for each n, but can be unbounded as n grows. -/
noncomputable def levelBranchBound (U : AmbientTree) (n : ℕ) : ℕ := by
  classical
  exact 1 + (U.levelSet_finite n).toFinset.sup
    (fun x : U => Nat.card (ChildIndex U x))

/-- Every level alphabet is nonempty. -/
theorem levelBranchBound_pos (U : AmbientTree) (n : ℕ) :
    0 < levelBranchBound U n := by
  unfold levelBranchBound
  omega

/-- The immediate children of any node at ambient rank n are
bounded by the finite level-dependent alphabet size. -/
theorem childCard_le_levelBranchBound
    (U : AmbientTree) (n : ℕ) {x : U}
    (hx : U.level x = n) :
    Nat.card (ChildIndex U x) ≤ levelBranchBound U n := by
  classical
  have hxMem : x ∈ (U.levelSet_finite n).toFinset := by
    simpa only [Set.Finite.mem_toFinset] using
      (show x ∈ U.levelSet n from hx)
  have hsup :
      Nat.card (ChildIndex U x) ≤
        (U.levelSet_finite n).toFinset.sup
          (fun z : U => Nat.card (ChildIndex U z)) :=
    Finset.le_sup (f := fun z : U => Nat.card (ChildIndex U z)) hxMem
  unfold levelBranchBound
  omega

/-- The level-dependent finite label type. -/
abbrev LevelAlphabet (U : AmbientTree) (n : ℕ) :=
  Fin (levelBranchBound U n)

/-- A surjection from the level alphabet onto the actual immediate
children of x exists, even when the degree of x differs from all
other nodes at its level. -/
theorem exists_childAlphabetMap
    (U : AmbientTree) (x : U) :
    ∃ f : LevelAlphabet U (U.level x) → ChildIndex U x,
      Function.Surjective f := by
  classical
  letI : Fintype (ChildIndex U x) := Fintype.ofFinite _
  have hle : Fintype.card (ChildIndex U x) ≤
      Fintype.card (LevelAlphabet U (U.level x)) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using
      (childCard_le_levelBranchBound U (U.level x) rfl)
  have hfun : Nonempty
      (LevelAlphabet U (U.level x) → ChildIndex U x) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty (ChildIndex U x))⟩
  exact Function.exists_surjective_iff.mpr
    ⟨hfun, Function.Embedding.nonempty_of_card_le hle⟩

/-- Pick one surjective local labeling of immediate ambient successors. -/
noncomputable def childAlphabetMap (U : AmbientTree) (x : U) :
    LevelAlphabet U (U.level x) → ChildIndex U x :=
  Classical.choose (exists_childAlphabetMap U x)

theorem childAlphabetMap_surjective (U : AmbientTree) (x : U) :
    Function.Surjective (childAlphabetMap U x) :=
  Classical.choose_spec (exists_childAlphabetMap U x)

/-- Every actual ambient immediate child has at least one abstract
letter labeling it, without a global branching-degree bound. -/
theorem exists_label_of_child
    (U : AmbientTree) {x y : U} (hxy : x ⋖ y) :
    ∃ a : LevelAlphabet U (U.level x),
      (childAlphabetMap U x a).1 = y := by
  obtain ⟨a, ha⟩ := childAlphabetMap_surjective U x ⟨y, hxy⟩
  exact ⟨a, congrArg Subtype.val ha⟩

end GeneralTree
end Milliken
