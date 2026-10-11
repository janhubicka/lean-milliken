import Milliken.GeneralTree.FrontierPartition
import Milliken.GeneralTree.SpliceCarrier

/-!
# The mixed protected-cone carrier for Todorčević A.3(2)

Let D be a strong background tree and X a strong refinement whose
source-level n frontier is contained in D's source-level j frontier.
Construct a candidate protected carrier:
  * retain all D nodes strictly before frontier j;
  * in the used frontier cones, retain exactly the X nodes;
  * in all other frontier cones, retain the D nodes.

The candidate preserves D's full j-th frontier, uses only X in
the descendant cones of the used X-frontier, and agrees with D
on all earlier selected levels. Both sectors are disjoint.

Proving this carrier is a genuine strong subtree still requires
alignment of the *later* selected levels of X and D, predecessor
closure, and ambient-successor uniqueness. Those tasks are not
assumed or claimed by this module.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A candidate protected strong-tree carrier. D supplies the
old finite prefix and the unused frontier tails; X supplies
the used frontier tails. -/
def mixedCarrier (D X : StrongSubtree U)
    (j n : ℕ) : Set U :=
  D.initialPart j ∪
    ({z : U | z ∈ X.carrier ∧
      z ∈ U.upwardCones (X.sourceLevel n)} ∪
     {z : U | z ∈ D.carrier ∧
      z ∈ U.upwardCones (D.sourceLevel j \ X.sourceLevel n)})

/-- If one entire selected frontier of X lies on D's
frontier, their selected ambient ranks coincide. -/
theorem frontier_levels_eq_of_subset
    (D X : StrongSubtree U)
    (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j) :
    X.levels n = D.levels j := by
  obtain ⟨x, hx⟩ := X.sourceLevel_nonempty n
  exact hx.2.symm.trans (hfront hx).2

/-- Every mixed-carrier node belongs to the union of the
two ambient strong-tree carriers. -/
theorem mixedCarrier_subset_union
    (D X : StrongSubtree U) (j n : ℕ) :
    D.mixedCarrier X j n ⊆ D.carrier ∪ X.carrier := by
  intro z hz
  rcases hz with hPrefix | (hUsed | hUnused)
  · exact Or.inl hPrefix.1
  · exact Or.inr hUsed.1
  · exact Or.inl hUnused.1

/-- The protected carrier coincides with D's selected levels
strictly before the mixing frontier. -/
theorem mixedCarrier_level_before
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    {k : ℕ} (hk : k < j) :
    {z : U | z ∈ D.mixedCarrier X j n ∧
      U.level z = D.levels k} =
        D.sourceLevel k := by
  have hmatch : X.levels n = D.levels j :=
    D.frontier_levels_eq_of_subset X j n hfront
  ext z
  constructor
  · rintro ⟨hz, hzLevel⟩
    rcases hz with hPrefix | (hUsed | hUnused)
    · exact ⟨hPrefix.1, hzLevel⟩
    · obtain ⟨_, p, hp, hpz⟩ := hUsed
      have hge : D.levels j ≤ U.level z := by
        calc
          D.levels j = X.levels n := hmatch.symm
          _ = U.level p := hp.2.symm
          _ ≤ U.level z := U.level_mono hpz
      have hlt := D.levels_strictMono hk
      rw [hzLevel] at hge
      omega
    · obtain ⟨_, p, hp, hpz⟩ := hUnused
      have hge : D.levels j ≤ U.level z := by
        calc
          D.levels j = U.level p := hp.1.2.symm
          _ ≤ U.level z := U.level_mono hpz
      have hlt := D.levels_strictMono hk
      rw [hzLevel] at hge
      omega
  · intro hz
    refine ⟨Or.inl ?_, hz.2⟩
    exact ⟨hz.1, k, hk, hz.2⟩

/-- The frontier level of the mixed carrier contains
*all* D-frontier nodes: used nodes from X and unused
nodes from D. -/
theorem mixedCarrier_level_at
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j) :
    {z : U | z ∈ D.mixedCarrier X j n ∧
      U.level z = D.levels j} =
        D.sourceLevel j := by
  have hmatch : X.levels n = D.levels j :=
    D.frontier_levels_eq_of_subset X j n hfront
  ext z
  constructor
  · rintro ⟨hz, hzLevel⟩
    rcases hz with hPrefix | (hUsed | hUnused)
    · have hlt := D.initialPart_level_lt j hPrefix
      rw [hzLevel] at hlt
      omega
    · have hzX : z ∈ X.sourceLevel n := by
        refine ⟨hUsed.1, ?_⟩
        exact hzLevel.trans hmatch.symm
      exact hfront hzX
    · obtain ⟨hzD, p, hp, hpz⟩ := hUnused
      have hpEq : p = z :=
        U.eq_of_le_of_level_eq hpz (hp.1.2.trans hzLevel.symm)
      have hpD : p ∈ D.sourceLevel j := hp.1
      rw [hpEq] at hpD
      exact hpD
  · intro hzD
    by_cases hzX : z ∈ X.sourceLevel n
    · refine ⟨Or.inr (Or.inl ?_), hzD.2⟩
      exact ⟨hzX.1, z, hzX, le_rfl⟩
    · refine ⟨Or.inr (Or.inr ?_), hzD.2⟩
      exact ⟨hzD.1, z, ⟨hzD, hzX⟩, le_rfl⟩

/-- **Relative used-cone protection**: any mixed-carrier
node in the upward cone of a used X-frontier node
belongs to X. This is the hypothesis of the proved
A.3(2) neighborhood-confinement lemma. -/
theorem mixedCarrier_used_sector_in_X
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    {z : U}
    (hz : z ∈ D.mixedCarrier X j n)
    (hcone : z ∈ U.upwardCones (X.sourceLevel n)) :
    z ∈ X.carrier := by
  have hmatch : X.levels n = D.levels j :=
    D.frontier_levels_eq_of_subset X j n hfront
  rcases hz with hPrefix | (hUsed | hUnused)
  · obtain ⟨p, hp, hpz⟩ := hcone
    have hge : D.levels j ≤ U.level z := by
      calc
        D.levels j = X.levels n := hmatch.symm
        _ = U.level p := hp.2.symm
        _ ≤ U.level z := U.level_mono hpz
    have hlt := D.initialPart_level_lt j hPrefix
    omega
  · exact hUsed.1
  · have hd :=
      D.frontier_used_unused_disjoint j
        (X.sourceLevel n) hfront
    exact ((Set.disjoint_left.mp hd) hcone hUnused.2).elim

/-- **Unused-cone protection**: mixed-carrier nodes in the
unused frontier cones belong to the background tree D.
This is symmetric to the used-X confinement lemma. -/
theorem mixedCarrier_unused_sector_in_D
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    {z : U}
    (hz : z ∈ D.mixedCarrier X j n)
    (hcone :
      z ∈ U.upwardCones (D.sourceLevel j \ X.sourceLevel n)) :
    z ∈ D.carrier := by
  rcases hz with hPrefix | (hUsed | hUnused)
  · exact hPrefix.1
  · have hd :=
      D.frontier_used_unused_disjoint j
        (X.sourceLevel n) hfront
    exact ((Set.disjoint_left.mp hd) hUsed.2 hcone).elim
  · exact hUnused.1

end StrongSubtree
end GeneralTree
end Milliken
