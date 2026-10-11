import Milliken.GeneralTree.SpliceCones

/-!
# A genuine arbitrary-tree strong-subtree graft

Let S and T be arbitrary infinite strong subtrees of a pruned, locally
finitely branching rooted tree U. When the source-level n frontier of S
lies on source level j of T, the splice that keeps S's first n levels
and the T-descendant tails of S's frontier is once again a genuine
infinite strong subtree.

The predecessor clause has three possible positions: inside the old
stem, crossing to the frontier, and entirely inside the T tail.
The ambient-successor uniqueness clause has two cases: source levels
before the frontier are controlled by S, those from the frontier
onwards are controlled by T.

No uniform branching alphabet or degree bound is used.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Every positive source level of the candidate graft has a
predecessor at the preceding spliced source level. -/
theorem spliceCarrier_predecessor_exists
    (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j)
    (k : ℕ) (z : U)
    (hz : z ∈ S.spliceCarrier T n)
    (hzlevel : U.level z = S.spliceLevels T n j (k + 1)) :
    ∃ p : U,
      p ∈ S.spliceCarrier T n ∧
      U.level p = S.spliceLevels T n j k ∧ p ≤ z := by
  by_cases hkcut : k + 1 ≤ n
  · have hk : k < n := by omega
    have hzS : z ∈ S.sourceLevel (k + 1) := by
      by_cases hnext : k + 1 < n
      · exact S.splice_source_before T hnext hz hzlevel
      · have heq : k + 1 = n := by omega
        have hzAt : U.level z = S.spliceLevels T n j n := by
          calc
            U.level z = S.spliceLevels T n j (k + 1) := hzlevel
            _ = S.spliceLevels T n j n :=
              congrArg (S.spliceLevels T n j) heq
        have hs := S.splice_source_at T n j hlevel
          (fun x hx => (htop hx).1) hz hzAt
        simpa only [heq] using hs
    obtain ⟨p, hp, hpl, hpz⟩ :=
      S.predecessor_exists k z hzS.1 hzS.2
    refine ⟨p, Or.inl ⟨hp, k, hk, hpl⟩, ?_, hpz⟩
    rw [S.spliceLevels_before T hk]
    exact hpl
  · have hk : n ≤ k := by omega
    have heq : k + 1 = n + ((k - n) + 1) := by omega
    have hzAt :
        U.level z =
          S.spliceLevels T n j (n + ((k - n) + 1)) := by
      calc
        U.level z = S.spliceLevels T n j (k + 1) := hzlevel
        _ = S.spliceLevels T n j (n + ((k - n) + 1)) :=
          congrArg (S.spliceLevels T n j) heq
    obtain ⟨hzT, hx⟩ :=
      S.splice_source_after T n j ((k - n) + 1) hlevel hz hzAt
    let m : ℕ := j + (k - n)
    have hztop : U.level z = T.levels (m + 1) := by
      have hidx : j + ((k - n) + 1) = m + 1 := by
        dsimp [m]
        omega
      simpa only [hidx] using hzT.2
    obtain ⟨p, hp, hpl, hpz⟩ :=
      T.predecessor_exists m z hzT.1 hztop
    have hzTail : z ∈ S.spliceTail T n := ⟨hzT.1, hx⟩
    have hplevel : T.levels j ≤ U.level p := by
      calc
        T.levels j ≤ T.levels m :=
          T.levels_strictMono.monotone (by dsimp [m]; omega)
        _ = U.level p := hpl.symm
    have hpTail : p ∈ S.spliceTail T n :=
      S.spliceTail_ancestor T n j hlevel hzTail hp hpz hplevel
    refine ⟨p, Or.inr hpTail, ?_, hpz⟩
    rw [S.spliceLevels_ge T hk]
    exact hpl

/-- Exactly one node on the next selected source level lies
above each ambient immediate-successor cone of a retained node. -/
theorem spliceCarrier_successor_unique
    (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j)
    (k : ℕ) (x : U)
    (hx : x ∈ S.spliceCarrier T n)
    (hxlevel : U.level x = S.spliceLevels T n j k)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U,
      z ∈ S.spliceCarrier T n ∧
      U.level z = S.spliceLevels T n j (k + 1) ∧ y ≤ z := by
  by_cases hk : k < n
  · have hxS : x ∈ S.sourceLevel k :=
      S.splice_source_before T hk hx hxlevel
    obtain ⟨z, hz, hunique⟩ :=
      S.successor_unique k x hxS.1 hxS.2 y hxy
    have hkstep : k + 1 ≤ n := by omega
    have hztop : z ∈ S.spliceCarrier T n := by
      by_cases hsmall : k + 1 < n
      · exact Or.inl ⟨hz.1, k + 1, hsmall, hz.2.1⟩
      · have hEq : k + 1 = n := by omega
        have hfrontier : z ∈ S.sourceLevel n := by
          have hstem : z ∈ S.sourceLevel (k + 1) :=
            ⟨hz.1, hz.2.1⟩
          simpa only [hEq] using hstem
        exact Or.inr ⟨(htop hfrontier).1,
          z, hfrontier, le_rfl⟩
    have hstepLevel :
        S.spliceLevels T n j (k + 1) = S.levels (k + 1) := by
      by_cases hsmall : k + 1 < n
      · exact S.spliceLevels_before T hsmall
      · have hEq : k + 1 = n := by omega
        rw [hEq]
        calc
          S.spliceLevels T n j n = T.levels j := by
            simpa only [Nat.add_zero] using
              (S.spliceLevels_at T n j 0)
          _ = S.levels n := hlevel.symm
    refine ⟨z, ⟨hztop, hz.2.1.trans hstepLevel.symm,
      hz.2.2⟩, ?_⟩
    intro w hw
    have hwS : w ∈ S.sourceLevel (k + 1) := by
      by_cases hsmall : k + 1 < n
      · exact S.splice_source_before T hsmall hw.1 hw.2.1
      · have hEq : k + 1 = n := by omega
        have hwAt : U.level w = S.spliceLevels T n j n := by
          calc
            U.level w = S.spliceLevels T n j (k + 1) := hw.2.1
            _ = S.spliceLevels T n j n :=
              congrArg (S.spliceLevels T n j) hEq
        have hs := S.splice_source_at T n j hlevel
          (fun z hz => (htop hz).1) hw.1 hwAt
        simpa only [hEq] using hs
    exact hunique w ⟨hwS.1, hwS.2, hw.2.2⟩
  · have hkge : n ≤ k := Nat.le_of_not_gt hk
    have hkEq : n + (k - n) = k := by omega
    have hxAt :
        U.level x =
          S.spliceLevels T n j (n + (k - n)) := by
      rw [hkEq]
      exact hxlevel
    obtain ⟨hxT, hxFrontier⟩ :=
      S.splice_source_after T n j (k - n) hlevel hx hxAt
    let m : ℕ := j + (k - n)
    obtain ⟨z, hz, hunique⟩ :=
      T.successor_unique m x hxT.1 hxT.2 y hxy
    have hxTail : x ∈ S.spliceTail T n :=
      ⟨hxT.1, hxFrontier⟩
    have hzTail : z ∈ S.spliceTail T n :=
      S.spliceTail_upward_in_T T n hxTail
        (hxy.le.trans hz.2.2) hz.1
    have hzNext :
        U.level z = S.spliceLevels T n j (k + 1) := by
      rw [S.spliceLevels_ge T (show n ≤ k + 1 by omega)]
      have hi : m + 1 = j + (k + 1 - n) := by
        dsimp [m]
        omega
      exact hz.2.1.trans (congrArg T.levels hi)
    refine ⟨z, ⟨Or.inr hzTail, hzNext, hz.2.2⟩, ?_⟩
    intro w hw
    have hkEqNext : n + (k + 1 - n) = k + 1 := by omega
    have hwAt :
        U.level w =
          S.spliceLevels T n j (n + (k + 1 - n)) := by
      rw [hkEqNext]
      exact hw.2.1
    obtain ⟨hwT, _⟩ :=
      S.splice_source_after T n j (k + 1 - n)
        hlevel hw.1 hwAt
    have hidx : j + (k + 1 - n) = m + 1 := by
      dsimp [m]
      omega
    have hwT' : w ∈ T.sourceLevel (m + 1) := by
      simpa only [hidx] using hwT
    exact hunique w ⟨hwT'.1, hwT'.2, hw.2.2⟩

/-- The positive-height splice is genuinely strong in the
arbitrary ambient tree. -/
noncomputable def spliceStrong
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    StrongSubtree U := by
  have hlevel : S.levels n = T.levels j := by
    obtain ⟨x, hx⟩ := S.sourceLevel_nonempty n
    exact hx.2.symm.trans (htop hx).2
  exact {
    carrier := S.spliceCarrier T n
    levels := S.spliceLevels T n j
    levels_strictMono := S.spliceLevels_strictMono T n j hlevel
    root := S.root
    root_mem := by
      by_cases hn : 0 < n
      · exact S.spliceCarrier_root_mem T hn
      · have hn0 : n = 0 := by omega
        subst n
        have hs : S.root ∈ S.sourceLevel 0 :=
          ⟨S.root_mem, S.root_level⟩
        exact Or.inr ⟨(htop hs).1, S.root, hs, le_rfl⟩
    root_level := by
      by_cases hn : 0 < n
      · rw [S.spliceLevels_before T hn]
        exact S.root_level
      · have hn0 : n = 0 := by omega
        subst n
        change U.level S.root = T.levels (j + (0 - 0))
        simpa only [Nat.zero_sub, Nat.add_zero] using
          S.root_level.trans hlevel
    root_below := by
      intro x hx
      exact S.spliceCarrier_root_below T n hx
    carrier_levels := by
      intro x hx
      exact S.spliceCarrier_levels T n j hlevel hx
    predecessor_exists := by
      intro k z hz hzlevel
      exact S.spliceCarrier_predecessor_exists T n j
        hlevel htop k z hz hzlevel
    successor_unique := by
      intro k x hx hxlevel y hxy
      exact S.spliceCarrier_successor_unique T n j
        hlevel htop k x hx hxlevel y hxy
  }

/-- The graft carrier is the explicit prefix-plus-tail set. -/
@[simp] theorem spliceStrong_carrier
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    (S.spliceStrong T n j htop).carrier =
      S.spliceCarrier T n := rfl

/-- All nodes of the graft lie in T if its retained finite
prefix already lies in T. -/
theorem spliceStrong_refines
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j)
    (hprefix : S.initialPart n ⊆ T.carrier) :
    (S.spliceStrong T n j htop).Refines T := by
  intro z hz
  change z ∈ S.spliceCarrier T n at hz
  rcases hz with hstem | htail
  · exact hprefix hstem
  · exact htail.1

end StrongSubtree
end GeneralTree
end Milliken
