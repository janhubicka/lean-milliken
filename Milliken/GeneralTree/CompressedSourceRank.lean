import Milliken.GeneralTree.CompressedSourceAmbient

/-!
# Ambient rank of the full compressed selected-source tree

The new AmbientTree has a genuinely different height function:
one compressed parent step crosses an arbitrary gap in the source
indices of the old tree. We show that its Mathlib AmbientTree.level
is exactly the selected compressed rank n, not the original
ambient rank S.levels(f n).

This identifies its complete level n with the *full* original
S.sourceLevel(f n), with no discarded old branches. Consequently
source-level density and the restricted somewhere-dense obstruction
can be transported through the future compressed product embedding
without silently changing their quantifier domains.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace CompressedSourceSelection

variable (S : StrongSubtree U) (f : CompressedSourceSelection)

/-- The actual rank of a compressed source-level node in its new
AmbientTree equals its selected-source index. -/
theorem compressedAmbient_level_eq_index
    (z : Node S f) :
    (compressedAmbientTree S f).level z = z.1 := by
  have aux :
      ∀ (n : ℕ) (x : Node S f), x.1 = n →
        (compressedAmbientTree S f).level x = n := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hbot : x = (⊥ : Node S f) :=
          node_eq_bot_of_index_zero S f x hx
        rw [hbot]
        exact (compressedAmbientTree S f).level_root
    | succ n ih =>
        intro x hx
        let p : Node S f := nodeParent S f x
        have hp : p.1 = n := by
          rw [nodeParent_index, hx]
          omega
        have hpx : p ≤ x := nodeParent_le S f x
        have hcov : p ⋖ x :=
          (node_covBy_iff S f p x).mpr
            ⟨hpx, by rw [hx, hp]⟩
        have hheight :=
          (compressedAmbientTree S f).level_covBy hcov
        have hpheight := ih p hp
        omega
  exact aux z.1 z rfl

/-- The nth compressed ambient level contains exactly the nodes
on the selected old source frontier f(n). -/
theorem compressedAmbient_levelSet_eq
    (n : ℕ) :
    (compressedAmbientTree S f).levelSet n =
      {z : Node S f | z.1 = n} := by
  ext z
  change ((compressedAmbientTree S f).level z = n) ↔ z.1 = n
  rw [compressedAmbient_level_eq_index S f z]

/-- Every new ambient level is finite. -/
theorem compressedAmbient_level_finite (n : ℕ) :
    ((compressedAmbientTree S f).levelSet n).Finite := by
  rw [compressedAmbient_levelSet_eq]
  exact node_level_finite S f n

/-- Every new ambient level is nonempty. -/
theorem compressedAmbient_level_nonempty (n : ℕ) :
    ((compressedAmbientTree S f).levelSet n).Nonempty := by
  rw [compressedAmbient_levelSet_eq]
  exact node_level_nonempty S f n

end CompressedSourceSelection
end GeneralTree
end Milliken
