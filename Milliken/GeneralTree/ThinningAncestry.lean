import Milliken.GeneralTree.ThinningLevels

/-!
# Root and predecessor geometry of arbitrary selected-level thinning

The recursively selected levels of a pruned locally finite strong tree B
are nonempty. Every selected node descends from the original root,
and every node on the successor selected level has a retained parent
on the preceding thinned level. Each node belongs to the intended
selected level B.levels(f k), so its source index is determined by
its ambient rank.

These are verified strongness prerequisites for constructing an
infinite strong subtree with the prescribed sparse selected levels.
The ambient-successor *uniqueness* clause is the remaining step.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- All recursively chosen thinning levels are nonempty. -/
theorem thinningLevel_nonempty
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) :
    (B.thinningLevel f hf hf0 k).Nonempty := by
  induction k with
  | zero =>
      rw [B.thinningLevel_zero f hf hf0]
      exact ⟨B.root, rfl⟩
  | succ k ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hxy⟩ := U.has_child x
      let x' : {v : U // v ∈ B.thinningLevel f hf hf0 k} :=
        ⟨x, hx⟩
      let child : ChildIndex U x := ⟨y, hxy⟩
      let z : U :=
        B.longConeRepresentative
          (hf (Nat.lt_succ_self k))
          (B.thinningLevel_subset_sourceLevel f hf hf0 k hx)
          child
      refine ⟨z, ?_⟩
      apply (B.thinningLevel_succ_iff f hf hf0 k z).2
      exact ⟨x', child, rfl⟩

/-- Every node on every recursively selected thinning level
is a descendant of B's distinguished root. -/
theorem thinningLevel_root_below
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) {z : U}
    (hz : z ∈ B.thinningLevel f hf hf0 k) :
    B.root ≤ z := by
  induction k generalizing z with
  | zero =>
      rw [B.thinningLevel_zero f hf hf0] at hz
      have heq : z = B.root := hz
      subst z
      exact le_rfl
  | succ k ih =>
      obtain ⟨x, y, hzy⟩ :=
        (B.thinningLevel_succ_iff f hf hf0 k z).mp hz
      have hroot : B.root ≤ x.1 := ih x.2
      have hxchild : x.1 ≤ (y : U) := y.2.le
      have hchildz :
          (y : U) ≤
            B.longConeRepresentative
              (hf (Nat.lt_succ_self k))
              (B.thinningLevel_subset_sourceLevel f hf hf0 k x.2)
              y :=
        (B.longConeRepresentative_spec
          (hf (Nat.lt_succ_self k))
          (B.thinningLevel_subset_sourceLevel f hf hf0 k x.2)
          y).2
      rw [hzy]
      exact hroot.trans (hxchild.trans hchildz)

/-- Each node selected on the next thinning level has
a retained predecessor on the preceding thinning level. -/
theorem thinningLevel_predecessor_exists
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) {z : U}
    (hz : z ∈ B.thinningLevel f hf hf0 (k + 1)) :
    ∃ x : U,
      x ∈ B.thinningLevel f hf hf0 k ∧
      U.level x = B.levels (f k) ∧ x ≤ z := by
  obtain ⟨x, y, hzy⟩ :=
    (B.thinningLevel_succ_iff f hf hf0 k z).mp hz
  have hxB :
      x.1 ∈ B.sourceLevel (f k) :=
    B.thinningLevel_subset_sourceLevel f hf hf0 k x.2
  refine ⟨x.1, x.2, hxB.2, ?_⟩
  rw [hzy]
  have hxy : x.1 ≤ (y : U) := y.2.le
  have hyz :=
    (B.longConeRepresentative_spec
      (hf (Nat.lt_succ_self k)) hxB y).2
  exact hxy.trans hyz

/-- The full candidate thinning carrier lies in B. -/
theorem thinningCarrier_subset
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    B.thinningCarrier f hf hf0 ⊆ B.carrier := by
  intro z hz
  change z ∈ ⋃ k : ℕ, B.thinningLevel f hf hf0 k at hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact (B.thinningLevel_subset_sourceLevel f hf hf0 k hk).1

/-- The distinguished root belongs to the thinning carrier. -/
theorem thinningCarrier_root_mem
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    B.root ∈ B.thinningCarrier f hf hf0 := by
  change B.root ∈ ⋃ k : ℕ, B.thinningLevel f hf hf0 k
  exact Set.mem_iUnion.mpr ⟨0, by
    rw [B.thinningLevel_zero f hf hf0]
    exact rfl⟩

/-- Every candidate carrier node descends from B's root. -/
theorem thinningCarrier_root_below
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    {z : U} (hz : z ∈ B.thinningCarrier f hf hf0) :
    B.root ≤ z := by
  change z ∈ ⋃ k : ℕ, B.thinningLevel f hf hf0 k at hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact B.thinningLevel_root_below f hf hf0 k hk

/-- A candidate carrier node at selected rank B.levels(f k)
must belong to exactly the recursively selected set at index k. -/
theorem thinningCarrier_at_level
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) {z : U}
    (hz : z ∈ B.thinningCarrier f hf hf0)
    (hzk : U.level z = B.levels (f k)) :
    z ∈ B.thinningLevel f hf hf0 k := by
  change z ∈ ⋃ ell : ℕ, B.thinningLevel f hf hf0 ell at hz
  obtain ⟨ell, hell⟩ := Set.mem_iUnion.mp hz
  have hlevel : B.levels (f ell) = B.levels (f k) :=
    (B.thinningLevel_subset_sourceLevel f hf hf0 ell hell).2.symm.trans hzk
  have hindex : ell = k :=
    hf.injective (B.levels_strictMono.injective hlevel)
  subst ell
  exact hell

/-- The carrier has an actual selected predecessor on each
positive prescribed source level. -/
theorem thinningCarrier_predecessor_exists
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) {z : U}
    (hz : z ∈ B.thinningCarrier f hf hf0)
    (hzk : U.level z = B.levels (f (k + 1))) :
    ∃ x : U,
      x ∈ B.thinningCarrier f hf hf0 ∧
      U.level x = B.levels (f k) ∧ x ≤ z := by
  have hzLevel : z ∈ B.thinningLevel f hf hf0 (k + 1) :=
    B.thinningCarrier_at_level f hf hf0 (k + 1) hz hzk
  obtain ⟨x, hx, hxLevel, hxz⟩ :=
    B.thinningLevel_predecessor_exists f hf hf0 k hzLevel
  refine ⟨x, ?_, hxLevel, hxz⟩
  change x ∈ ⋃ ell : ℕ, B.thinningLevel f hf hf0 ell
  exact Set.mem_iUnion.mpr ⟨k, hx⟩

end StrongSubtree
end GeneralTree
end Milliken
