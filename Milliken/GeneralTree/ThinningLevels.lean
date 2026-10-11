import Milliken.GeneralTree.LongCones

/-!
# Dependent recursive levels for arbitrary strong-tree thinning

Given a strong tree B and a strictly increasing map f : ℕ → ℕ
with f(0)=0, we recursively select levels of a new tree on
B's source levels f(k). The root level consists of B.root.
From each selected node at level k we choose one representative
at level f(k+1) inside every *ambient immediate child* cone.

The recursion stores, as part of its type, the proof that every
selected node belongs to B's designated source level. This makes
the recursive choice genuinely well typed when the ambient
number of children varies from node to node.

These are candidate levels; the eventual `StrongSubtree` still
requires uniqueness across predecessor cones, predecessor closure,
and root-below properties. No thinning theorem is claimed here.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Successive selected sets for thinning B to a prescribed
subsequence of its selected source levels. The membership
invariant is carried by a dependent subtype. -/
noncomputable def thinningLevelData
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    (k : ℕ) →
      {s : Set U // s ⊆ B.sourceLevel (f k)} :=
  Nat.rec
    (motive := fun k => {s : Set U // s ⊆ B.sourceLevel (f k)})
    (⟨{B.root}, by
      intro z hz
      have heq : z = B.root := hz
      subst z
      rw [hf0]
      exact ⟨B.root_mem, B.root_level⟩⟩)
    (fun k prev =>
      ⟨{z : U |
          ∃ x : {v : U // v ∈ prev.1},
            ∃ y : ChildIndex U x.1,
              z = B.longConeRepresentative
                    (hf (Nat.lt_succ_self k))
                    (prev.2 x.2) y},
        by
          intro z hz
          obtain ⟨x, y, rfl⟩ := hz
          exact (B.longConeRepresentative_spec
            (hf (Nat.lt_succ_self k))
            (prev.2 x.2) y).1⟩)

/-- The actual selected node set at source index k. -/
noncomputable def thinningLevel
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) : Set U :=
  (B.thinningLevelData f hf hf0 k).1

/-- Every recursively selected node is on the intended
ambient selected level of B. -/
theorem thinningLevel_subset_sourceLevel
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) :
    B.thinningLevel f hf hf0 k ⊆ B.sourceLevel (f k) :=
  (B.thinningLevelData f hf hf0 k).2

/-- The first thinning level is exactly B's root singleton. -/
theorem thinningLevel_zero
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    B.thinningLevel f hf hf0 0 = {B.root} := by
  rfl

/-- The successor thinning level is the image of all typed
ambient child cones of nodes on the preceding thinning level
under the long-cone representative choice. -/
theorem thinningLevel_succ_iff
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) (z : U) :
    z ∈ B.thinningLevel f hf hf0 (k + 1) ↔
      ∃ x : {v : U // v ∈ B.thinningLevel f hf hf0 k},
        ∃ y : ChildIndex U x.1,
          z = B.longConeRepresentative
                (hf (Nat.lt_succ_self k))
                ((B.thinningLevel_subset_sourceLevel
                    f hf hf0 k) x.2) y := by
  rfl

/-- The thinning carrier is the union of the recursively
selected levels. -/
noncomputable def thinningCarrier
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    Set U :=
  ⋃ k : ℕ, B.thinningLevel f hf hf0 k

/-- Every node in the thinning carrier has a source index
at which its ambient level agrees with B.levels(f k). -/
theorem thinningCarrier_levels
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    {z : U} (hz : z ∈ B.thinningCarrier f hf hf0) :
    ∃ k : ℕ, U.level z = B.levels (f k) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  refine ⟨k, ?_⟩
  exact (B.thinningLevel_subset_sourceLevel f hf hf0 k hk).2

end StrongSubtree
end GeneralTree
end Milliken
