import Milliken.GeneralTree.BoundaryGraftPredecessor

/-!
# Unique ambient successor representatives for boundary grafts

In the inverse A.4 boundary construction, keep an arbitrary finite
strong stem and replace its n-th selected boundary cones by genuinely
strong coordinate refinements synchronized to one common level map.
This module proves the full successor-uniqueness obligation across
the graft cut and in each coordinate tail.

The cut case is essential: each ambient immediate-child cone of the
old top stem node is represented by exactly one old T-boundary
coordinate. Its selected F-root is therefore the *unique* new
graft representative in that cone. In the tail, ancestor separation
forces every candidate successor into the same coordinate factor.

No homogeneous alphabet, regular-branching hypothesis or global
branching-degree bound appears.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

theorem boundaryGraft_successor_succ
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T (n + 1) → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T (n + 1) i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M)
    (k : ℕ) (x : U)
    (hx : x ∈ T.boundaryGraftCarrier (n + 1) F)
    (hxlevel :
      U.level x = T.boundaryGraftLevels (n + 1) M k)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U,
      z ∈ T.boundaryGraftCarrier (n + 1) F ∧
      U.level z = T.boundaryGraftLevels (n + 1) M (k + 1) ∧
      y ≤ z := by
  by_cases hOld : k + 1 < n + 1
  · have hk : k < n + 1 := by omega
    have hxlevelT : U.level x = T.levels k := by
      rw [T.boundaryGraftLevels_before (n + 1) M hk] at hxlevel
      exact hxlevel
    have hxT : x ∈ T.sourceLevel k := by
      have hset :
          x ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level w = T.levels k} := ⟨hx, hxlevelT⟩
      rw [T.boundaryGraft_level_before (n + 1) F hF hk] at hset
      exact hset
    obtain ⟨z, hz, hunique⟩ :=
      T.successor_unique k x hxT.1 hxT.2 y hxy
    have hzlevelG :
        U.level z = T.boundaryGraftLevels (n + 1) M (k + 1) := by
      rw [T.boundaryGraftLevels_before (n + 1) M hOld]
      exact hz.2.1
    refine ⟨z, ⟨Or.inl ⟨hz.1, k + 1, hOld, hz.2.1⟩,
      hzlevelG, hz.2.2⟩, ?_⟩
    intro w hw
    have hwlevelT : U.level w = T.levels (k + 1) := by
      calc
        U.level w =
            T.boundaryGraftLevels (n + 1) M (k + 1) := hw.2.1
        _ = T.levels (k + 1) :=
          T.boundaryGraftLevels_before (n + 1) M hOld
    have hwT : w ∈ T.sourceLevel (k + 1) := by
      have hset :
          w ∈ {v : U | v ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level v = T.levels (k + 1)} := ⟨hw.1, hwlevelT⟩
      rw [T.boundaryGraft_level_before (n + 1) F hF hOld] at hset
      exact hset
    exact hunique w ⟨hwT.1, hwT.2, hw.2.2⟩
  · by_cases hCut : k + 1 = n + 1
    · have hk : k = n := by omega
      subst k
      have hxlevelT : U.level x = T.levels n := by
        calc
          U.level x = T.boundaryGraftLevels (n + 1) M n :=
            hxlevel
          _ = T.levels n :=
            T.boundaryGraftLevels_before
              (n + 1) M (Nat.lt_succ_self n)
      have hxT : x ∈ T.sourceLevel n := by
        have hset :
            x ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
              U.level w = T.levels n} := ⟨hx, hxlevelT⟩
        rw [T.boundaryGraft_level_before
          (n + 1) F hF (Nat.lt_succ_self n)] at hset
        exact hset
      obtain ⟨q, hq, huniqueT⟩ :=
        T.successor_unique n x hxT.1 hxT.2 y hxy
      let i : SourceBoundary T (n + 1) := ⟨q, hq.1, hq.2.1⟩
      have hroot : i.1 ≤ (F i).root :=
        ((hF i) (F i).root_mem).2
      have hlevelAt :
          T.boundaryGraftLevels (n + 1) M (n + 1) = M 0 := by
        simpa only [Nat.add_zero] using
          T.boundaryGraftLevels_at (n + 1) M 0
      have hzlevelG :
          U.level (F i).root =
            T.boundaryGraftLevels (n + 1) M (n + 1) := by
        calc
          U.level (F i).root = (F i).levels 0 := (F i).root_level
          _ = M 0 := congrFun (hlevels i) 0
          _ = T.boundaryGraftLevels (n + 1) M (n + 1) :=
            hlevelAt.symm
      refine ⟨(F i).root,
        ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, (F i).root_mem⟩),
          hzlevelG, hq.2.2.trans hroot⟩, ?_⟩
      intro w hw
      have hwM : U.level w = M 0 :=
        hw.2.1.trans hlevelAt
      have hwSet :
          w ∈ {v : U | v ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level v = M 0} := ⟨hw.1, hwM⟩
      rw [T.boundaryGraft_level_at (n + 1) F M hF hlevels] at hwSet
      obtain ⟨j, hjw⟩ := hwSet
      have hrootw : j.1 ≤ w := by
        calc
          j.1 ≤ (F j).root := ((hF j) (F j).root_mem).2
          _ = w := hjw
      have hyrank : U.level y ≤ U.level j.1 := by
        have hstep := U.level_covBy hxy
        have hstrict :=
          T.levels_strictMono (Nat.lt_succ_self n)
        have hrankj : U.level j.1 = T.levels (n + 1) := j.2.2
        omega
      have hyj : y ≤ j.1 :=
        U.le_of_common_descendant_of_level_le hw.2.2 hrootw hyrank
      have hjq : j.1 = q :=
        huniqueT j.1 ⟨j.2.1, j.2.2, hyj⟩
      have hji : j = i := Subtype.ext hjq
      calc
        w = (F j).root := hjw.symm
        _ = (F i).root := congrArg (fun v => (F v).root) hji
    · have hk : n + 1 ≤ k := by omega
      let t : ℕ := k - (n + 1)
      have hkEq : k = n + 1 + t := by dsimp [t]; omega
      have hkNext : k + 1 = n + 1 + (t + 1) := by dsimp [t]; omega
      have hxM : U.level x = M t := by
        calc
          U.level x = T.boundaryGraftLevels (n + 1) M k := hxlevel
          _ = T.boundaryGraftLevels (n + 1) M (n + 1 + t) :=
            by rw [hkEq]
          _ = M t := T.boundaryGraftLevels_at (n + 1) M t
      have hxSet :
          x ∈ {w : U | w ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level w = M t} := ⟨hx, hxM⟩
      rw [T.boundaryGraft_level_after
        (n + 1) F M hF hlevels hM t] at hxSet
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxSet
      obtain ⟨z, hz, hunique⟩ :=
        (F i).successor_unique t x hxi.1 hxi.2 y hxy
      have hzG :
          U.level z =
            T.boundaryGraftLevels (n + 1) M (k + 1) := by
        calc
          U.level z = (F i).levels (t + 1) := hz.2.1
          _ = M (t + 1) := congrFun (hlevels i) (t + 1)
          _ = T.boundaryGraftLevels (n + 1) M (k + 1) := by
            rw [hkNext, T.boundaryGraftLevels_at]
      refine ⟨z,
        ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, hz.1⟩), hzG, hz.2.2⟩,
        ?_⟩
      intro w hw
      have hwM : U.level w = M (t + 1) := by
        calc
          U.level w =
              T.boundaryGraftLevels (n + 1) M (k + 1) := hw.2.1
          _ = T.boundaryGraftLevels (n + 1) M
              (n + 1 + (t + 1)) := by rw [hkNext]
          _ = M (t + 1) :=
            T.boundaryGraftLevels_at (n + 1) M (t + 1)
      have hwSet :
          w ∈ {v : U | v ∈ T.boundaryGraftCarrier (n + 1) F ∧
            U.level v = M (t + 1)} := ⟨hw.1, hwM⟩
      rw [T.boundaryGraft_level_after
        (n + 1) F M hF hlevels hM (t + 1)] at hwSet
      obtain ⟨j, hwj⟩ := Set.mem_iUnion.mp hwSet
      have hiX : i.1 ≤ x := ((hF i) hxi.1).2
      have hjW : j.1 ≤ w := ((hF j) hwj.1).2
      have hiW : i.1 ≤ w :=
        hiX.trans (hxy.le.trans hw.2.2)
      have hlevelsIJ : U.level i.1 = U.level j.1 :=
        i.2.2.trans j.2.2.symm
      have hIJ : i.1 = j.1 := by
        rcases le_total_of_directed hiW hjW with hji | hij
        · exact (U.eq_of_le_of_level_eq hji hlevelsIJ.symm).symm
        · exact U.eq_of_le_of_level_eq hij hlevelsIJ
      have hij : i = j := Subtype.ext hIJ
      have hwFi : w ∈ (F i).sourceLevel (t + 1) := by
        rw [hij]
        exact hwj
      exact hunique w ⟨hwFi.1, hwFi.2, hw.2.2⟩

end StrongSubtree
end GeneralTree
end Milliken
