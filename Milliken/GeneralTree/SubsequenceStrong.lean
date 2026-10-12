import Milliken.GeneralTree.ChosenStrong

/-!
# Selecting any increasing source-level subsequence of a strong tree

The existing \`thinStrong\` construction fixes the original root
and therefore requires f(0)=0. In the Halpern--Läuchli
monochromatic-level fusion one first selects an infinite set of
successful levels and may discard an arbitrary initial prefix.

The chosen-strong-subtree constructor gives this generalization:
choose any retained root on source level f(0), and then take the
canonical long-cone representative for every ambient child on
source level f(k+1). The resulting strong subtree has prescribed
ambient levels B.levels(f k), refines B, and retains no more than
B's actual f(k)-th source level at the kth new source level.

This is purely order geometry for arbitrary locally finite
trees with unbounded node-dependent branching.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A coherent family of actual child-cone representatives for
any strictly increasing source-index subsequence, including when
the first index is positive. -/
noncomputable def subsequenceChoice
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    LevelChoice B f where
  root := Classical.choose (B.sourceLevel_nonempty (f 0))
  root_mem := Classical.choose_spec (B.sourceLevel_nonempty (f 0))
  next := fun k x hx y =>
    B.longConeRepresentative (hf (Nat.lt_succ_self k)) hx y
  next_mem := by
    intro k x hx y
    exact (B.longConeRepresentative_spec
      (hf (Nat.lt_succ_self k)) hx y).1
  next_above := by
    intro k x hx y
    exact (B.longConeRepresentative_spec
      (hf (Nat.lt_succ_self k)) hx y).2

/-- A genuine strong subtree selecting an arbitrary increasing
subsequence of source indices, with a root on the first
selected source level. -/
noncomputable def subsequenceStrong
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    StrongSubtree U :=
  (B.subsequenceChoice f hf).toStrongSubtree hf

theorem subsequenceStrong_refines
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    (B.subsequenceStrong f hf).Refines B :=
  (B.subsequenceChoice f hf).toStrongSubtree_refines hf

theorem subsequenceStrong_levels
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    (B.subsequenceStrong f hf).levels =
      fun k => B.levels (f k) :=
  (B.subsequenceChoice f hf).toStrongSubtree_levels hf

theorem subsequenceStrong_sourceLevel_subset
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f)
    (k : ℕ) :
    (B.subsequenceStrong f hf).sourceLevel k ⊆
      B.sourceLevel (f k) := by
  rw [subsequenceStrong,
    LevelChoice.toStrongSubtree_sourceLevel]
  exact (B.subsequenceChoice f hf).level_subset_sourceLevel k

theorem subsequenceStrong_root_sourceLevel
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) :
    (B.subsequenceStrong f hf).root ∈ B.sourceLevel (f 0) :=
  (B.subsequenceChoice f hf).root_mem

end StrongSubtree
end GeneralTree
end Milliken
