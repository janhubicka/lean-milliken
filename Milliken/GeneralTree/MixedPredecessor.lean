import Milliken.GeneralTree.MixedLevels
import Milliken.GeneralTree.SpliceCones

/-!
# Selected predecessor closure for a mixed protected strong-tree carrier

Suppose the used X-frontier lies in D's selected frontier and the
future selected ambient levels of X and D are synchronized.
Every node on a positive mixed selected level has a retained
predecessor on the preceding mixed level.

Before the mixing frontier use D's predecessor law.
After the frontier, in a used cone use X's predecessor law;
in an unused cone use D's. The selected predecessor remains
in its same sector because both it and the sector's frontier
node are ancestors of the original node and their ambient
ranks are ordered.

This establishes the predecessor field for the pending mixed
StrongSubtree constructor. Ambient child-cone uniqueness is
the remaining genuine strongness proof.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Every selected mixed node at source level k+1 has a
retained mixed predecessor on source level k. -/
theorem mixedCarrier_predecessor_exists
    (D X : StrongSubtree U) (j n k : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    (z : U)
    (hz : z ∈ D.mixedCarrier X j n)
    (hzlevel : U.level z = D.levels (k + 1)) :
    ∃ p : U,
      p ∈ D.mixedCarrier X j n ∧
      U.level p = D.levels k ∧ p ≤ z := by
  by_cases hbefore : k + 1 ≤ j
  · have hzD : z ∈ D.sourceLevel (k + 1) := by
      by_cases hlt : k + 1 < j
      · have hmember :
            z ∈ {w : U |
              w ∈ D.mixedCarrier X j n ∧
              U.level w = D.levels (k + 1)} :=
          ⟨hz, hzlevel⟩
        rw [D.mixedCarrier_level_before X j n hfront hlt]
          at hmember
        exact hmember
      · have heq : k + 1 = j := by omega
        have hmember :
            z ∈ {w : U |
              w ∈ D.mixedCarrier X j n ∧
              U.level w = D.levels j} := by
          refine ⟨hz, ?_⟩
          simpa only [heq] using hzlevel
        rw [D.mixedCarrier_level_at X j n hfront] at hmember
        simpa only [heq] using hmember
    obtain ⟨p, hp, hpLevel, hpz⟩ :=
      D.predecessor_exists k z hzD.1 hzD.2
    have hk : k < j := by omega
    exact ⟨p, Or.inl ⟨hp, k, hk, hpLevel⟩, hpLevel, hpz⟩
  · have hkj : j ≤ k := by omega
    have hhigh : D.levels j ≤ U.level z := by
      calc
        D.levels j ≤ D.levels (k + 1) :=
          D.levels_strictMono.monotone (by omega)
        _ = U.level z := hzlevel.symm
    rcases hz with hPrefix | (hUsed | hUnused)
    · have hlt := D.initialPart_level_lt j hPrefix
      omega
    · obtain ⟨hzX, p, hp, hpz⟩ := hUsed
      have hidx : j + (k + 1 - j) = k + 1 := by omega
      have hzXLevel :
          U.level z = X.levels (n + (k + 1 - j)) := by
        calc
          U.level z = D.levels (k + 1) := hzlevel
          _ = D.levels (j + (k + 1 - j)) := by rw [hidx]
          _ = X.levels (n + (k + 1 - j)) :=
            hlevels (k + 1 - j)
      have hpredidx :
          n + (k + 1 - j) = (n + (k - j)) + 1 := by
        omega
      have hzSucc :
          U.level z = X.levels ((n + (k - j)) + 1) := by
        rw [← hpredidx]
        exact hzXLevel
      obtain ⟨q, hq, hqLevel, hqz⟩ :=
        X.predecessor_exists (n + (k - j))
          z hzX hzSucc
      have hpqrank : U.level p ≤ U.level q := by
        calc
          U.level p = X.levels n := hp.2
          _ ≤ X.levels (n + (k - j)) :=
            X.levels_strictMono.monotone (by omega)
          _ = U.level q := hqLevel.symm
      have hpq : p ≤ q :=
        U.le_of_common_descendant_of_level_le hpz hqz hpqrank
      have hqMixed : q ∈ D.mixedCarrier X j n :=
        Or.inr (Or.inl ⟨hq, p, hp, hpq⟩)
      have hqRank : U.level q = D.levels k := by
        have hidxK : j + (k - j) = k := by omega
        calc
          U.level q = X.levels (n + (k - j)) := hqLevel
          _ = D.levels (j + (k - j)) :=
            (hlevels (k - j)).symm
          _ = D.levels k := by rw [hidxK]
      exact ⟨q, hqMixed, hqRank, hqz⟩
    · obtain ⟨hzD, p, hp, hpz⟩ := hUnused
      obtain ⟨q, hq, hqLevel, hqz⟩ :=
        D.predecessor_exists k z hzD hzlevel
      have hpqRank : U.level p ≤ U.level q := by
        calc
          U.level p = D.levels j := hp.1.2
          _ ≤ D.levels k :=
            D.levels_strictMono.monotone hkj
          _ = U.level q := hqLevel.symm
      have hpq : p ≤ q :=
        U.le_of_common_descendant_of_level_le hpz hqz hpqRank
      exact ⟨q,
        Or.inr (Or.inr ⟨hq, p, hp, hpq⟩),
        hqLevel, hqz⟩

end StrongSubtree
end GeneralTree
end Milliken
