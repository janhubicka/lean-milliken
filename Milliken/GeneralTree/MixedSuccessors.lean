import Milliken.GeneralTree.MixedPredecessor

/-!
# Unique ambient-successor representatives in protected mixed cones

The mixed carrier of D and X, with synchronized future selected
levels and X's used frontier contained in D's selected frontier,
satisfies the exact strong-subtree successor uniqueness condition.

Before the protected frontier every node and next-level candidate
belongs to D. At or beyond the frontier, retained nodes lie in
either a used X-sector or unused D-sector. The appropriate tree's
successor uniqueness supplies a representative; upward closure
and the proved sector confinement force every competing
representative into the same tree.

No global degree bound or homogeneous branching is used.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The mixed carrier has exactly D's source levels on all
levels up to and including the protected frontier j. -/
theorem mixedCarrier_level_le
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    {k : ℕ} (hk : k ≤ j) :
    {z : U | z ∈ D.mixedCarrier X j n ∧
      U.level z = D.levels k} =
        D.sourceLevel k := by
  rcases lt_or_eq_of_le hk with hlt | heq
  · exact D.mixedCarrier_level_before X j n hfront hlt
  · subst k
    exact D.mixedCarrier_level_at X j n hfront

/-- Every ambient immediate child cone of a retained mixed node
contains exactly one representative at the next selected level. -/
theorem mixedCarrier_successor_unique
    (D X : StrongSubtree U) (j n k : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    (x : U)
    (hx : x ∈ D.mixedCarrier X j n)
    (hxLevel : U.level x = D.levels k)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U,
      z ∈ D.mixedCarrier X j n ∧
      U.level z = D.levels (k + 1) ∧ y ≤ z := by
  by_cases hk : k < j
  · have hxD : x ∈ D.sourceLevel k := by
      have hmember :
          x ∈ {w : U | w ∈ D.mixedCarrier X j n ∧
            U.level w = D.levels k} := ⟨hx, hxLevel⟩
      rw [D.mixedCarrier_level_le X j n hfront (by omega : k ≤ j)]
        at hmember
      exact hmember
    obtain ⟨z, hz, hunique⟩ :=
      D.successor_unique k x hxD.1 hxD.2 y hxy
    have hzMixed : z ∈ D.mixedCarrier X j n := by
      have hmember :
          z ∈ {w : U | w ∈ D.mixedCarrier X j n ∧
            U.level w = D.levels (k + 1)} := by
        rw [D.mixedCarrier_level_le X j n hfront
          (show k + 1 ≤ j by omega)]
        exact ⟨hz.1, hz.2.1⟩
      exact hmember.1
    refine ⟨z, ⟨hzMixed, hz.2.1, hz.2.2⟩, ?_⟩
    intro w hw
    have hwD : w ∈ D.sourceLevel (k + 1) := by
      have hmember :
          w ∈ {z : U | z ∈ D.mixedCarrier X j n ∧
            U.level z = D.levels (k + 1)} :=
        ⟨hw.1, hw.2.1⟩
      rw [D.mixedCarrier_level_le X j n hfront
        (show k + 1 ≤ j by omega)] at hmember
      exact hmember
    exact hunique w ⟨hwD.1, hwD.2, hw.2.2⟩
  · have hkj : j ≤ k := by omega
    have hxNotPrefix : x ∉ D.initialPart j := by
      intro hprefix
      have hlt := D.initialPart_level_lt j hprefix
      have hge : D.levels j ≤ D.levels k :=
        D.levels_strictMono.monotone hkj
      rw [hxLevel] at hlt
      omega
    rcases hx with hPrefix | (hUsed | hUnused)
    · exact (hxNotPrefix hPrefix).elim
    · have hidxK : j + (k - j) = k := by omega
      have hxX : x ∈ X.sourceLevel (n + (k - j)) := by
        refine ⟨hUsed.1, ?_⟩
        calc
          U.level x = D.levels k := hxLevel
          _ = D.levels (j + (k - j)) := by rw [hidxK]
          _ = X.levels (n + (k - j)) := hlevels (k - j)
      obtain ⟨z, hz, hunique⟩ :=
        X.successor_unique (n + (k - j))
          x hxX.1 hxX.2 y hxy
      have hzCone :
          z ∈ U.upwardCones (X.sourceLevel n) :=
        U.upwardCones_upwards (X.sourceLevel n)
          hUsed.2 (hxy.le.trans hz.2.2)
      have hzMixed : z ∈ D.mixedCarrier X j n :=
        Or.inr (Or.inl ⟨hz.1, hzCone⟩)
      have hidxNext : j + (k + 1 - j) = k + 1 := by omega
      have hidxX :
          n + (k - j) + 1 = n + (k + 1 - j) := by omega
      have hzLevel : U.level z = D.levels (k + 1) := by
        calc
          U.level z = X.levels (n + (k - j) + 1) := hz.2.1
          _ = X.levels (n + (k + 1 - j)) := by rw [hidxX]
          _ = D.levels (j + (k + 1 - j)) :=
            (hlevels (k + 1 - j)).symm
          _ = D.levels (k + 1) := by rw [hidxNext]
      refine ⟨z, ⟨hzMixed, hzLevel, hz.2.2⟩, ?_⟩
      intro w hw
      have hwCone :
          w ∈ U.upwardCones (X.sourceLevel n) :=
        U.upwardCones_upwards (X.sourceLevel n)
          hUsed.2 (hxy.le.trans hw.2.2)
      have hwX : w ∈ X.carrier :=
        D.mixedCarrier_used_sector_in_X X j n
          hfront hw.1 hwCone
      have hwXrank :
          U.level w = X.levels (n + (k - j) + 1) := by
        calc
          U.level w = D.levels (k + 1) := hw.2.1
          _ = D.levels (j + (k + 1 - j)) := by rw [hidxNext]
          _ = X.levels (n + (k + 1 - j)) :=
            hlevels (k + 1 - j)
          _ = X.levels (n + (k - j) + 1) := by rw [hidxX]
      exact hunique w ⟨hwX, hwXrank, hw.2.2⟩
    · have hxD : x ∈ D.sourceLevel k :=
        ⟨hUnused.1, hxLevel⟩
      obtain ⟨z, hz, hunique⟩ :=
        D.successor_unique k x hxD.1 hxD.2 y hxy
      let F : Set U := D.sourceLevel j \ X.sourceLevel n
      have hzCone : z ∈ U.upwardCones F :=
        U.upwardCones_upwards F hUnused.2
          (hxy.le.trans hz.2.2)
      have hzMixed : z ∈ D.mixedCarrier X j n :=
        Or.inr (Or.inr ⟨hz.1, hzCone⟩)
      refine ⟨z, ⟨hzMixed, hz.2.1, hz.2.2⟩, ?_⟩
      intro w hw
      have hwCone : w ∈ U.upwardCones F :=
        U.upwardCones_upwards F hUnused.2
          (hxy.le.trans hw.2.2)
      have hwD : w ∈ D.carrier :=
        D.mixedCarrier_unused_sector_in_D X j n
          hfront hw.1 hwCone
      exact hunique w ⟨hwD, hw.2.1, hw.2.2⟩

end StrongSubtree
end GeneralTree
end Milliken
