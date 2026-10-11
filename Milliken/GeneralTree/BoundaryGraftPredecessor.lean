import Milliken.GeneralTree.BoundaryGraftData

/-!
# Selected predecessor closure of heterogeneous boundary grafts

For a nonempty finite stem, the boundary graft retains the old
source levels below the cut and uses a finite family of genuinely
strong successor cones with one common level sequence from the cut
onward. Every graft node on a positive source level has a predecessor
on the immediately preceding *selected* level.

This is one of the genuinely strong-tree obligations for the inverse
Halpern--Läuchli boundary tuple constructor. There is no global bound
on the number of children of the ambient tree.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Every positive source level of the candidate nonempty-stem
boundary graft has a predecessor at the preceding graft level. -/
theorem boundaryGraft_predecessor_succ
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T (n + 1) → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T (n + 1) i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M)
    (k : ℕ) (z : U)
    (hz : z ∈ T.boundaryGraftCarrier (n + 1) F)
    (hzlevel :
      U.level z = T.boundaryGraftLevels (n + 1) M (k + 1)) :
    ∃ p : U,
      p ∈ T.boundaryGraftCarrier (n + 1) F ∧
      U.level p = T.boundaryGraftLevels (n + 1) M k ∧
      p ≤ z := by
  by_cases hOld : k + 1 < n + 1
  · have hk : k < n + 1 := by omega
    have hzOldLevel : U.level z = T.levels (k + 1) := by
      rw [T.boundaryGraftLevels_before (n + 1) M hOld] at hzlevel
      exact hzlevel
    have hzT : z ∈ T.sourceLevel (k + 1) := by
      have hzSet :
          z ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level w = T.levels (k + 1)} :=
        ⟨hz, hzOldLevel⟩
      rw [T.boundaryGraft_level_before (n + 1) F hF hOld] at hzSet
      exact hzSet
    obtain ⟨p, hp, hpl, hpz⟩ :=
      T.predecessor_exists k z hzT.1 hzT.2
    refine ⟨p, Or.inl ⟨hp, k, hk, hpl⟩, ?_, hpz⟩
    rw [T.boundaryGraftLevels_before (n + 1) M hk]
    exact hpl
  · by_cases hCut : k + 1 = n + 1
    · have hk : k = n := by omega
      subst k
      have hzM : U.level z = M 0 := by
        calc
          U.level z =
              T.boundaryGraftLevels (n + 1) M (n + 1) := hzlevel
          _ = M 0 := by
            simpa only [Nat.add_zero] using
              T.boundaryGraftLevels_at (n + 1) M 0
      have hzSet :
          z ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level w = M 0} := ⟨hz, hzM⟩
      rw [T.boundaryGraft_level_at (n + 1) F M hF hlevels] at hzSet
      obtain ⟨i, hi⟩ := hzSet
      have hzi : (F i).root = z := hi
      rw [← hzi]
      obtain ⟨p, hp, hpl, hpz⟩ :=
        T.predecessor_exists n i.1 i.2.1 i.2.2
      have hroot : i.1 ≤ (F i).root :=
        ((hF i) (F i).root_mem).2
      refine ⟨p, Or.inl ⟨hp, n, Nat.lt_succ_self n, hpl⟩, ?_,
        hpz.trans hroot⟩
      rw [T.boundaryGraftLevels_before
        (n + 1) M (Nat.lt_succ_self n)]
      exact hpl
    · have hk : n + 1 ≤ k := by omega
      let t : ℕ := k - (n + 1)
      have hkEq : k = n + 1 + t := by dsimp [t]; omega
      have hkNext : k + 1 = n + 1 + (t + 1) := by dsimp [t]; omega
      have hzM : U.level z = M (t + 1) := by
        calc
          U.level z =
              T.boundaryGraftLevels (n + 1) M (k + 1) := hzlevel
          _ = T.boundaryGraftLevels (n + 1) M
              (n + 1 + (t + 1)) := by rw [hkNext]
          _ = M (t + 1) := T.boundaryGraftLevels_at (n + 1) M (t + 1)
      have hzSet :
          z ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level w = M (t + 1)} := ⟨hz, hzM⟩
      rw [T.boundaryGraft_level_after
        (n + 1) F M hF hlevels hM (t + 1)] at hzSet
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzSet
      obtain ⟨p, hp, hpl, hpz⟩ :=
        (F i).predecessor_exists t z hi.1 hi.2
      refine ⟨p, Or.inr (Set.mem_iUnion.mpr ⟨i, hp⟩), ?_, hpz⟩
      calc
        U.level p = (F i).levels t := hpl
        _ = M t := congrFun (hlevels i) t
        _ = T.boundaryGraftLevels (n + 1) M k := by
          rw [hkEq, T.boundaryGraftLevels_at]

end StrongSubtree
end GeneralTree
end Milliken
