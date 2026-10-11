import Milliken.GeneralTree.SpliceCarrier

/-!
# Exact source-level and carrier laws for an arbitrary-tree stem graft

The candidate strong-tree splice keeps S's initial source levels
before n and then follows T's levels from j onward, but only
within the descendant cones of S's n-th frontier.

The lemmas here prove the exact levels of this candidate carrier,
its distinguished root, and its closure under further T-descendants.
This is the geometric preparation for the strongness constructor
and the positive-height A.3 amalgamation proof.

All statements apply to arbitrary pruned locally finitely branching
ambient rooted trees with no globally bounded branching degree.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The spliced ambient-level map follows T after the cut. -/
theorem spliceLevels_ge (S T : StrongSubtree U)
    {n j k : ℕ} (hk : n ≤ k) :
    S.spliceLevels T n j k =
      T.levels (j + (k - n)) := by
  simp [spliceLevels, not_lt.mpr hk]

/-- The tail is upward closed *within T*. -/
theorem spliceTail_upward_in_T
    (S T : StrongSubtree U) (n : ℕ)
    {z w : U}
    (hz : z ∈ S.spliceTail T n)
    (hzw : z ≤ w) (hwT : w ∈ T.carrier) :
    w ∈ S.spliceTail T n := by
  obtain ⟨_, x, hx, hxz⟩ := hz
  exact ⟨hwT, x, hx, hxz.trans hzw⟩

/-- At the k-th level beyond the splice frontier the candidate
carrier is exactly the T-level in the descendant cones of the
selected S-frontier. -/
theorem spliceCarrier_level_tail
    (S T : StrongSubtree U)
    (n j k : ℕ)
    (hlevel : S.levels n = T.levels j) :
    {z : U |
      z ∈ S.spliceCarrier T n ∧
        U.level z = S.spliceLevels T n j (n + k)} =
      {z : U | z ∈ T.sourceLevel (j + k) ∧
        ∃ x : U, x ∈ S.sourceLevel n ∧ x ≤ z} := by
  ext z
  rw [S.spliceLevels_at T n j k]
  constructor
  · rintro ⟨hz, hzlevel⟩
    rcases hz with hprefix | htail
    · have hlt := S.initialPart_level_lt n hprefix
      have hle : T.levels j ≤ T.levels (j + k) :=
        T.levels_strictMono.monotone (by omega)
      rw [hzlevel] at hlt
      rw [hlevel] at hlt
      omega
    · obtain ⟨ht, x, hx, hxz⟩ := htail
      exact ⟨⟨ht, hzlevel⟩, x, hx, hxz⟩
  · rintro ⟨⟨ht, hzlevel⟩, x, hx, hxz⟩
    exact ⟨Or.inr ⟨ht, x, hx, hxz⟩, hzlevel⟩

/-- Every node of the candidate graft has one of the
spliced selected levels. This is the carrier-level clause of
the eventual strong-subtree constructor. -/
theorem spliceCarrier_levels
    (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j)
    {z : U} (hz : z ∈ S.spliceCarrier T n) :
    ∃ k : ℕ,
      U.level z = S.spliceLevels T n j k := by
  rcases hz with hprefix | htail
  · obtain ⟨_, k, hk, hzk⟩ := hprefix
    refine ⟨k, ?_⟩
    rw [S.spliceLevels_before T hk]
    exact hzk
  · obtain ⟨hzT, x, hx, hxz⟩ := htail
    obtain ⟨m, hm⟩ := T.carrier_levels z hzT
    have hge : T.levels j ≤ T.levels m := by
      calc
        T.levels j = S.levels n := hlevel.symm
        _ = U.level x := hx.2.symm
        _ ≤ U.level z := U.level_mono hxz
        _ = T.levels m := hm
    have hjm : j ≤ m := by
      by_contra hnot
      have hmj : m < j := Nat.lt_of_not_ge hnot
      have hstrict := T.levels_strictMono hmj
      omega
    refine ⟨n + (m - j), ?_⟩
    rw [S.spliceLevels_at T n j (m - j)]
    have hindex : j + (m - j) = m := by omega
    rw [hindex]
    exact hm

/-- For n positive, the root of S belongs to the candidate graft. -/
theorem spliceCarrier_root_mem (S T : StrongSubtree U)
    {n : ℕ} (hn : 0 < n) :
    S.root ∈ S.spliceCarrier T n := by
  apply Or.inl
  exact ⟨S.root_mem, 0, hn, S.root_level⟩

/-- The root of S is below every candidate graft node. -/
theorem spliceCarrier_root_below (S T : StrongSubtree U)
    (n : ℕ) {z : U}
    (hz : z ∈ S.spliceCarrier T n) :
    S.root ≤ z := by
  rcases hz with hprefix | htail
  · exact S.root_below z hprefix.1
  · obtain ⟨_, x, hx, hxz⟩ := htail
    exact (S.root_below x hx.1).trans hxz

/-- A selected node of the candidate graft on a tail level
belongs to T. This will let the strongness proof invoke the
actual T-successor relation at that level. -/
theorem spliceCarrier_tail_level_mem_T
    (S T : StrongSubtree U)
    (n j k : ℕ)
    (hlevel : S.levels n = T.levels j)
    {z : U}
    (hz : z ∈ S.spliceCarrier T n)
    (hzlevel :
      U.level z = S.spliceLevels T n j (n + k)) :
    z ∈ T.carrier := by
  have hh :
      z ∈ {w : U |
        w ∈ S.spliceCarrier T n ∧
          U.level w = S.spliceLevels T n j (n + k)} :=
    ⟨hz, hzlevel⟩
  rw [S.spliceCarrier_level_tail T n j k hlevel] at hh
  exact hh.1.1

end StrongSubtree
end GeneralTree
end Milliken
