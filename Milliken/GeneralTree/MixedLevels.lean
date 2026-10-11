import Milliken.GeneralTree.MixedCarrier

/-!
# Root and selected-level laws for the protected mixed frontier carrier

Let D be a strong background tree whose frontier j contains the
used frontier X.sourceLevel n. Assume from those frontiers onward
the two trees share the same selected ambient ranks:
  D.levels(j+t) = X.levels(n+t).
Then every node of their mixed carrier lies on one of D's
selected levels. The original D-root is retained and lies below
every mixed node. If D and X are refinements of B, the entire
candidate carrier is contained in B.

This verifies the root, regularity and ambient-refinement
prerequisites for the mixed strong-subtree constructor. The
remaining proofs are selected predecessors and exact one-node
representatives in every ambient child cone.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The original root of D is retained, also when the
mixing frontier is D's source level zero. -/
theorem mixedCarrier_root_mem
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j) :
    D.root ∈ D.mixedCarrier X j n := by
  by_cases hj : j = 0
  · subst j
    have hRoot : D.root ∈ D.sourceLevel 0 :=
      ⟨D.root_mem, D.root_level⟩
    have hAt :
        D.root ∈ {z : U |
          z ∈ D.mixedCarrier X 0 n ∧
          U.level z = D.levels 0} := by
      rw [D.mixedCarrier_level_at X 0 n hfront]
      exact hRoot
    exact hAt.1
  · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
    exact Or.inl ⟨D.root_mem, 0, hjpos, D.root_level⟩

/-- The root of D lies below all nodes of the mixed carrier. -/
theorem mixedCarrier_root_below
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    {z : U} (hz : z ∈ D.mixedCarrier X j n) :
    D.root ≤ z := by
  rcases hz with hPrefix | (hUsed | hUnused)
  · exact D.root_below z hPrefix.1
  · obtain ⟨_, p, hp, hpz⟩ := hUsed
    exact (D.root_below p (hfront hp).1).trans hpz
  · exact D.root_below z hUnused.1

/-- The mixed carrier uses only D's selected level sequence when
the used X-cones have the same future ambient levels. -/
theorem mixedCarrier_levels
    (D X : StrongSubtree U) (j n : ℕ)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    {z : U} (hz : z ∈ D.mixedCarrier X j n) :
    ∃ k : ℕ, U.level z = D.levels k := by
  rcases hz with hPrefix | (hUsed | hUnused)
  · obtain ⟨_, k, hk, hzLevel⟩ := hPrefix
    exact ⟨k, hzLevel⟩
  · obtain ⟨hzX, p, hp, hpz⟩ := hUsed
    obtain ⟨m, hm⟩ := X.carrier_levels z hzX
    have hnm : n ≤ m := by
      have hge : X.levels n ≤ X.levels m := by
        calc
          X.levels n = U.level p := hp.2.symm
          _ ≤ U.level z := U.level_mono hpz
          _ = X.levels m := hm
      by_contra hbad
      have hmn : m < n := Nat.lt_of_not_ge hbad
      have hlt := X.levels_strictMono hmn
      omega
    refine ⟨j + (m - n), ?_⟩
    have heq : n + (m - n) = m := by omega
    calc
      U.level z = X.levels m := hm
      _ = X.levels (n + (m - n)) := by rw [heq]
      _ = D.levels (j + (m - n)) :=
        (hlevels (m - n)).symm
  · obtain ⟨hzD, _⟩ := hUnused
    exact D.carrier_levels z hzD

/-- If both input strong trees refine B, so does the
mixed candidate carrier. -/
theorem mixedCarrier_subset_of_common_refinement
    (B D X : StrongSubtree U) (j n : ℕ)
    (hDB : D.Refines B)
    (hXB : X.Refines B) :
    D.mixedCarrier X j n ⊆ B.carrier := by
  intro z hz
  rcases hz with hPrefix | (hUsed | hUnused)
  · exact hDB hPrefix.1
  · exact hXB hUsed.1
  · exact hDB hUnused.1

end StrongSubtree
end GeneralTree
end Milliken
