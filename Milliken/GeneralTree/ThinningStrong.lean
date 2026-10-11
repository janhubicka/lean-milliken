import Milliken.GeneralTree.ThinningAncestry

/-!
# Thinning any arbitrary locally finite strong tree to selected levels

Given an infinite strong tree B and any strictly increasing map
f : ℕ → ℕ with f 0 = 0, the dependent recursive levels built in
ThinningLevels form a genuine strong subtree of the same ambient U.

The key final clause is uniqueness in every immediate ambient child
cone. A candidate node on the next thinning level is represented
by a previous-stage parent p and one of its immediate children.
If it lies in a specified cone of x, then x and p have a common
descendant and the same ambient rank, so x=p. The two ambient
children then have a common descendant and the same parent,
so they agree. This forces the representative to be the
canonical selected representative for the specified cone.

No fixed alphabet, homogeneous branching assumption, or
global bound on local branching degrees is needed.
-/

namespace Milliken

namespace AmbientTree

/-- Two ancestors of the same node at the same ambient rank
are equal in a rooted tree. -/
theorem eq_of_common_descendant_of_level_eq
    (U : AmbientTree)
    {x y z : U}
    (hx : x ≤ z) (hy : y ≤ z)
    (heq : U.level x = U.level y) :
    x = y := by
  rcases le_total_of_directed hx hy with hyx | hxy
  · exact (U.eq_of_le_of_level_eq hyx heq.symm).symm
  · exact U.eq_of_le_of_level_eq hxy heq

end AmbientTree

namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The recursively thinned next source level has exactly one
representative in every ambient child cone of each retained node. -/
theorem thinningLevel_successor_unique
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) {x : U}
    (hx : x ∈ B.thinningLevel f hf hf0 k)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U,
      z ∈ B.thinningLevel f hf hf0 (k + 1) ∧ y ≤ z := by
  classical
  have hxB : x ∈ B.sourceLevel (f k) :=
    B.thinningLevel_subset_sourceLevel f hf hf0 k hx
  let yy : ChildIndex U x := ⟨y, hxy⟩
  let z : U :=
    B.longConeRepresentative (hf (Nat.lt_succ_self k)) hxB yy
  have hzIn : z ∈ B.thinningLevel f hf hf0 (k + 1) := by
    apply (B.thinningLevel_succ_iff f hf hf0 k z).2
    exact ⟨⟨x, hx⟩, yy, rfl⟩
  have hyz : y ≤ z :=
    (B.longConeRepresentative_spec
      (hf (Nat.lt_succ_self k)) hxB yy).2
  refine ⟨z, ⟨hzIn, hyz⟩, ?_⟩
  intro w hw
  obtain ⟨⟨p, hp⟩, u, hwRep⟩ :=
    (B.thinningLevel_succ_iff f hf hf0 k w).mp hw.1
  have hpB : p ∈ B.sourceLevel (f k) :=
    B.thinningLevel_subset_sourceLevel f hf hf0 k hp
  have hpW : p ≤ w := by
    rw [hwRep]
    have hpu : p ≤ (u : U) := u.2.le
    have huw :=
      (B.longConeRepresentative_spec
        (hf (Nat.lt_succ_self k)) hpB u).2
    exact hpu.trans huw
  have hxW : x ≤ w := hxy.le.trans hw.2
  have hlevel : U.level p = U.level x :=
    hpB.2.trans hxB.2.symm
  have hpx : p = x :=
    U.eq_of_common_descendant_of_level_eq hpW hxW hlevel
  subst p
  have huW : (u : U) ≤ w := by
    rw [hwRep]
    exact (B.longConeRepresentative_spec
      (hf (Nat.lt_succ_self k)) hpB u).2
  have hyu : y = (u : U) :=
    immediateChildren_eq_of_common_descendant U
      hxy u.2 hw.2 huW
  have hSub : u = yy := Subtype.ext hyu.symm
  subst u
  simpa only [z, yy] using hwRep

/-- Thin B to the prescribed selected level subsequence, obtaining
a genuine ambient strong subtree. -/
noncomputable def thinStrong
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    StrongSubtree U where
  carrier := B.thinningCarrier f hf hf0
  levels := fun k => B.levels (f k)
  levels_strictMono := B.levels_strictMono.comp hf
  root := B.root
  root_mem := B.thinningCarrier_root_mem f hf hf0
  root_level := by
    simpa only [hf0] using B.root_level
  root_below := by
    intro x hx
    exact B.thinningCarrier_root_below f hf hf0 hx
  carrier_levels := by
    intro x hx
    exact B.thinningCarrier_levels f hf hf0 hx
  predecessor_exists := by
    intro k z hz hlevel
    exact B.thinningCarrier_predecessor_exists f hf hf0 k hz hlevel
  successor_unique := by
    intro k x hx hxlevel y hxy
    have hxStage : x ∈ B.thinningLevel f hf hf0 k :=
      B.thinningCarrier_at_level f hf hf0 k hx hxlevel
    obtain ⟨z, hz, hunique⟩ :=
      B.thinningLevel_successor_unique f hf hf0 k hxStage y hxy
    refine ⟨z, ⟨?_, ?_, hz.2⟩, ?_⟩
    · change z ∈ ⋃ ell : ℕ, B.thinningLevel f hf hf0 ell
      exact Set.mem_iUnion.mpr ⟨k + 1, hz.1⟩
    · exact (B.thinningLevel_subset_sourceLevel
        f hf hf0 (k + 1) hz.1).2
    · intro w hw
      have hwStage : w ∈ B.thinningLevel f hf hf0 (k + 1) :=
        B.thinningCarrier_at_level f hf hf0
          (k + 1) hw.1 hw.2.1
      exact hunique w ⟨hwStage, hw.2.2⟩

/-- The thinning is a strong refinement of B. -/
theorem thinStrong_refines
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0) :
    (B.thinStrong f hf hf0).Refines B :=
  B.thinningCarrier_subset f hf hf0

/-- The source level of the genuine thinning is exactly the
recursively selected finite node set at that stage. -/
theorem thinStrong_sourceLevel
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ) :
    (B.thinStrong f hf hf0).sourceLevel k =
      B.thinningLevel f hf hf0 k := by
  ext z
  constructor
  · rintro ⟨hz, hlevel⟩
    exact B.thinningCarrier_at_level f hf hf0 k hz hlevel
  · intro hz
    refine ⟨?_, ?_⟩
    · change z ∈ ⋃ ell : ℕ, B.thinningLevel f hf hf0 ell
      exact Set.mem_iUnion.mpr ⟨k, hz⟩
    · exact (B.thinningLevel_subset_sourceLevel f hf hf0 k hz).2

end StrongSubtree
end GeneralTree
end Milliken
