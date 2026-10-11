import Milliken.GeneralTree.BoundaryTuple

/-!
# The candidate inverse boundary graft: carrier and level geometry

Given the finite T-boundary index at source height n and a family of
strong refinements of its actual successor cones, we keep T's first n
source levels and use the chosen cone refinements thereafter.

The key hypotheses are *only* coordinatewise refinement and a common
strictly increasing ambient-level map M. In particular neither a
constant alphabet nor a uniform branching-degree bound is introduced.

This module verifies the candidate's level map, ambient containment,
and its initial finite source-level geometry. Packaging the carrier
as a genuine StrongSubtree (including predecessors and ambient
successor-uniqueness) is a separate proof obligation; none of these
lemmas asserts the missing general Halpern--Läuchli theorem or A.4.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The proposed A.4 graft: the old finite stem and the selected
successor-cone refinements. -/
def boundaryGraftCarrier
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U) : Set U :=
  T.initialPart n ∪ ⋃ i, (F i).carrier

/-- Common selected levels for the candidate graft. -/
def boundaryGraftLevels
    (T : StrongSubtree U) (n : ℕ)
    (M : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k < n then T.levels k else M (k - n)

/-- The graft leaves each of the first n source levels intact. -/
theorem boundaryGraftLevels_before
    (T : StrongSubtree U) (n : ℕ) (M : ℕ → ℕ)
    {k : ℕ} (hk : k < n) :
    T.boundaryGraftLevels n M k = T.levels k := by
  simp [boundaryGraftLevels, hk]

/-- The first grafted level is M 0, and subsequent levels follow M. -/
theorem boundaryGraftLevels_at
    (T : StrongSubtree U) (n : ℕ) (M : ℕ → ℕ)
    (k : ℕ) :
    T.boundaryGraftLevels n M (n + k) = M k := by
  have hnot : ¬ n + k < n := by omega
  have hidx : n + k - n = k := by omega
  simp [boundaryGraftLevels, hnot, hidx]

/-- The common cone level sequence starts on or above T's nth level.
Every finite boundary has a genuine coordinate, even if branching is
unbounded over the whole ambient tree. -/
theorem boundaryGraft_start_le
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M) :
    T.levels n ≤ M 0 := by
  classical
  let i : SourceBoundary T n := Classical.choice (sourceBoundary_nonempty T n)
  have hroot : (F i).root ∈ (boundaryCones T n i).carrier :=
    hF i (F i).root_mem
  have hile : i.1 ≤ (F i).root := hroot.2
  calc
    T.levels n = U.level i.1 := i.2.2.symm
    _ ≤ U.level (F i).root := U.level_mono hile
    _ = (F i).levels 0 := (F i).root_level
    _ = M 0 := congrFun (hlevels i) 0

/-- Grafting at any finite stem preserves a strictly increasing
common level sequence. -/
theorem boundaryGraftLevels_strictMono
    (T : StrongSubtree U) (n : ℕ)
    (M : ℕ → ℕ)
    (hM : StrictMono M) (hstart : T.levels n ≤ M 0) :
    StrictMono (T.boundaryGraftLevels n M) := by
  apply strictMono_nat_of_lt_succ
  intro k
  by_cases hsmall : k + 1 < n
  · have hk : k < n := by omega
    rw [T.boundaryGraftLevels_before n M hk,
        T.boundaryGraftLevels_before n M hsmall]
    exact T.levels_strictMono (Nat.lt_succ_self k)
  · by_cases hk : k < n
    · have hnext : T.boundaryGraftLevels n M (k + 1) = M 0 := by
        have heq : k + 1 = n := by omega
        rw [heq]
        simpa only [Nat.add_zero] using
          (T.boundaryGraftLevels_at n M 0)
      rw [T.boundaryGraftLevels_before n M hk, hnext]
      exact lt_of_lt_of_le (T.levels_strictMono hk) hstart
    · have hk0 : ¬ k < n := hk
      have hk1 : ¬ k + 1 < n := by omega
      have hindex : k - n < k + 1 - n := by omega
      simpa [boundaryGraftLevels, hk0, hk1] using hM hindex

/-- Every node in the graft carrier is still a node of T. -/
theorem boundaryGraftCarrier_refines
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i)) :
    T.boundaryGraftCarrier n F ⊆ T.carrier := by
  intro z hz
  rcases hz with hprefix | htail
  · exact hprefix.1
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htail
    exact (boundaryCones_refines T n i) (hF i hi)

/-- At every retained stem level the candidate has exactly the
original source-level nodes: a cone refinement cannot introduce
ghost nodes into the protected prefix. -/
theorem boundaryGraft_level_before
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    {k : ℕ} (hk : k < n) :
    {z : U | z ∈ T.boundaryGraftCarrier n F ∧
      U.level z = T.levels k} = T.sourceLevel k := by
  ext z
  constructor
  · rintro ⟨hz, hlevel⟩
    rcases hz with hprefix | htail
    · exact ⟨hprefix.1, hlevel⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htail
      have hile : i.1 ≤ z := (hF i hi).2
      have hge : U.level i.1 ≤ U.level z := U.level_mono hile
      have hlt : T.levels k < T.levels n :=
        T.levels_strictMono hk
      have hirank : U.level i.1 = T.levels n := i.2.2
      omega
  · intro hz
    exact ⟨Or.inl ⟨hz.1, k, hk, hz.2⟩, hz.2⟩

/-- At the first new common level the candidate consists of
exactly the roots of the selected cone refinements, one for
each actual T boundary coordinate. -/
theorem boundaryGraft_level_at
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M) :
    {z : U | z ∈ T.boundaryGraftCarrier n F ∧
      U.level z = M 0} =
        Set.range (fun i : SourceBoundary T n => (F i).root) := by
  ext z
  constructor
  · rintro ⟨hz, hzlevel⟩
    rcases hz with hprefix | htail
    · have hlt : U.level z < T.levels n :=
        T.initialPart_level_lt n hprefix
      have hstart : T.levels n ≤ M 0 :=
        T.boundaryGraft_start_le n F M hF hlevels
      omega
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htail
      have hzero : z ∈ (F i).sourceLevel 0 := by
        refine ⟨hi, ?_⟩
        exact hzlevel.trans (congrFun (hlevels i) 0).symm
      have hroot : z = (F i).root := by
        simpa only [(F i).sourceLevel_zero_eq_singleton,
          Set.mem_singleton_iff] using hzero
      exact ⟨i, hroot.symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Or.inr (Set.mem_iUnion.mpr ⟨i, (F i).root_mem⟩), ?_⟩
    exact (F i).root_level.trans (congrFun (hlevels i) 0)

end StrongSubtree
end GeneralTree
end Milliken
