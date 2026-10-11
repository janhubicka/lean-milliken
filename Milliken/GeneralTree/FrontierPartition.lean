import Milliken.GeneralTree.ThinningStrong
import Milliken.GeneralTree.Ancestry

/-!
# Partition of the tail by selected frontier cones

In any rooted tree, descendants of different nodes of the same
ambient rank are disjoint. For a strong tree B and one of its
selected frontiers F=B.sourceLevel n, the cones above a chosen
subset of F and the cones above the remaining frontier nodes
therefore form a disjoint partition of all nodes descending
from F.

Every retained B-node at or beyond this selected ambient rank
belongs to exactly one such cone. This provides the geometric
separation of used and unused frontier sectors in A.3(2).
No uniform bound on branching degree is assumed.
-/

namespace Milliken
namespace AmbientTree

/-- All ambient descendants of at least one node in a set. -/
def upwardCones (U : AmbientTree) (F : Set U) : Set U :=
  {z | ∃ p : U, p ∈ F ∧ p ≤ z}

/-- A cone remains a cone under further ambient descendants. -/
theorem upwardCones_upwards (U : AmbientTree)
    (F : Set U) {z w : U}
    (hz : z ∈ U.upwardCones F) (hzw : z ≤ w) :
    w ∈ U.upwardCones F := by
  obtain ⟨p, hp, hpz⟩ := hz
  exact ⟨p, hp, hpz.trans hzw⟩

/-- The upward cones of a union are the union of the upward cones. -/
theorem upwardCones_union (U : AmbientTree)
    (F G : Set U) :
    U.upwardCones (F ∪ G) =
      U.upwardCones F ∪ U.upwardCones G := by
  ext z
  constructor
  · rintro ⟨p, hp, hpz⟩
    rcases hp with hpF | hpG
    · exact Or.inl ⟨p, hpF, hpz⟩
    · exact Or.inr ⟨p, hpG, hpz⟩
  · rintro (⟨p, hpF, hpz⟩ | ⟨p, hpG, hpz⟩)
    · exact ⟨p, Or.inl hpF, hpz⟩
    · exact ⟨p, Or.inr hpG, hpz⟩

/-- Equal-rank, disjoint frontiers have disjoint descendant cones. -/
theorem upwardCones_disjoint_of_same_rank (U : AmbientTree)
    (F G : Set U) (L : ℕ)
    (hF : ∀ p ∈ F, U.level p = L)
    (hG : ∀ q ∈ G, U.level q = L)
    (hFG : Disjoint F G) :
    Disjoint (U.upwardCones F) (U.upwardCones G) := by
  apply Set.disjoint_left.mpr
  intro z hzF hzG
  obtain ⟨p, hp, hpz⟩ := hzF
  obtain ⟨q, hq, hqz⟩ := hzG
  have hpq : p = q :=
    U.eq_of_common_descendant_of_level_eq hpz hqz
      ((hF p hp).trans (hG q hq).symm)
  have hpG : p ∈ G := by
    rw [hpq]
    exact hq
  exact (Set.disjoint_left.mp hFG) hp hpG

end AmbientTree

namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Descendant cones above used frontier nodes are disjoint
from the cones above unused nodes on the same frontier. -/
theorem frontier_used_unused_disjoint
    (B : StrongSubtree U) (n : ℕ)
    (Used : Set U)
    (hUsed : Used ⊆ B.sourceLevel n) :
    Disjoint
      (U.upwardCones Used)
      (U.upwardCones (B.sourceLevel n \ Used)) := by
  apply U.upwardCones_disjoint_of_same_rank
    Used (B.sourceLevel n \ Used) (B.levels n)
  · intro p hp
    exact (hUsed hp).2
  · intro p hp
    exact hp.1.2
  · apply Set.disjoint_left.mpr
    intro p hp hdiff
    exact hdiff.2 hp

/-- The used and unused frontier cones cover all descendant cones
of B's whole selected frontier. -/
theorem frontier_used_unused_union
    (B : StrongSubtree U) (n : ℕ)
    (Used : Set U)
    (hUsed : Used ⊆ B.sourceLevel n) :
    U.upwardCones (B.sourceLevel n) =
      U.upwardCones Used ∪
        U.upwardCones (B.sourceLevel n \ Used) := by
  ext z
  constructor
  · rintro ⟨p, hp, hpz⟩
    by_cases hpu : p ∈ Used
    · exact Or.inl ⟨p, hpu, hpz⟩
    · exact Or.inr ⟨p, ⟨hp, hpu⟩, hpz⟩
  · rintro (⟨p, hp, hpz⟩ | ⟨p, hp, hpz⟩)
    · exact ⟨p, hUsed hp, hpz⟩
    · exact ⟨p, hp.1, hpz⟩

/-- Every B-node at or after source level n belongs to
a cone of that selected frontier. -/
theorem carrier_mem_frontier_cones_of_level_ge
    (B : StrongSubtree U) (n : ℕ)
    {z : U} (hz : z ∈ B.carrier)
    (hlevel : B.levels n ≤ U.level z) :
    z ∈ U.upwardCones (B.sourceLevel n) := by
  obtain ⟨k, hk⟩ := B.carrier_levels z hz
  have hnk : n ≤ k := by
    by_contra hbad
    have hkn : k < n := Nat.lt_of_not_ge hbad
    have hstrict := B.levels_strictMono hkn
    omega
  obtain ⟨p, hp, hpz⟩ :=
    B.exists_sourceLevel_ancestor hnk ⟨hz, hk⟩
  exact ⟨p, hp, hpz⟩

/-- Each retained B-tail node is in a used frontier cone
or an unused frontier cone, and the two alternatives are
mutually exclusive. -/
theorem carrier_used_or_unused_frontier
    (B : StrongSubtree U) (n : ℕ)
    (Used : Set U)
    (hUsed : Used ⊆ B.sourceLevel n)
    {z : U} (hz : z ∈ B.carrier)
    (hlevel : B.levels n ≤ U.level z) :
    (z ∈ U.upwardCones Used) ∨
      (z ∈ U.upwardCones (B.sourceLevel n \ Used)) := by
  have hfrontier :
      z ∈ U.upwardCones (B.sourceLevel n) :=
    B.carrier_mem_frontier_cones_of_level_ge n hz hlevel
  rw [B.frontier_used_unused_union n Used hUsed] at hfrontier
  exact hfrontier

end StrongSubtree
end GeneralTree
end Milliken
