import Milliken.GeneralTree.FrontierUniqueness

/-!
# Carrier and level geometry of a general strong-tree stem graft

A finite strong stem comes from an infinite strong tree S. To extend it
with a different infinite strong tree T, keep the selected levels of S
strictly before its last stem level n and keep, from T, precisely
those nodes above the selected frontier S_n. The first tail level
then consists of the stem's frontier nodes themselves.

The new candidate carrier does not require a global bound on the
branching degree. The results below verify its source-level
geometry and the strictly increasing spliced levels. Packaging
this carrier as a StrongSubtree and proving the A.3 graft laws
are the next tasks; no such theorem is claimed here.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- Tail of T lying above some selected level-n frontier node of S. -/
def spliceTail (S T : StrongSubtree U) (n : ℕ) : Set U :=
  {z | z ∈ T.carrier ∧
    ∃ x : U, x ∈ S.sourceLevel n ∧ x ≤ z}

/-- Candidate graft carrier: the first n selected source levels of S
and the T-tail above the n-th frontier of S. -/
def spliceCarrier (S T : StrongSubtree U) (n : ℕ) : Set U :=
  S.initialPart n ∪ S.spliceTail T n

/-- The graft uses the levels of S before n, and the levels of T
from its j-th source level onwards, assuming the stem frontier
agrees with that level of T. -/
def spliceLevels (S T : StrongSubtree U)
    (n j k : ℕ) : ℕ :=
  if k < n then S.levels k
  else T.levels (j + (k - n))

theorem spliceLevels_before (S T : StrongSubtree U)
    {n j k : ℕ} (hk : k < n) :
    S.spliceLevels T n j k = S.levels k := by
  simp [spliceLevels, hk]

theorem spliceLevels_at (S T : StrongSubtree U)
    (n j k : ℕ) :
    S.spliceLevels T n j (n + k) = T.levels (j + k) := by
  have hnk : ¬ n + k < n := by omega
  simp [spliceLevels, hnk]

/-- The spliced level sequence is strictly increasing as long as
the selected frontier levels of S and T agree. -/
theorem spliceLevels_strictMono (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j) :
    StrictMono (S.spliceLevels T n j) := by
  apply strictMono_nat_of_lt_succ
  intro k
  by_cases hsmall : k + 1 < n
  · have hk : k < n := by omega
    rw [S.spliceLevels_before T hk,
        S.spliceLevels_before T hsmall]
    exact S.levels_strictMono (Nat.lt_succ_self k)
  · by_cases hk : k < n
    · have hkn : k + 1 = n := by omega
      have hkNext : ¬ k + 1 < n := hsmall
      rw [S.spliceLevels_before T hk]
      change S.levels k <
        (if k + 1 < n then S.levels (k + 1)
         else T.levels (j + (k + 1 - n)))
      rw [if_neg hkNext]
      have hidx : j + (k + 1 - n) = j := by omega
      rw [hidx, ← hlevel, ← hkn]
      exact S.levels_strictMono (Nat.lt_succ_self k)
    · have hkn : ¬ k < n := hk
      have hnext : ¬ k + 1 < n := by omega
      change
        (if k < n then S.levels k
         else T.levels (j + (k - n))) <
        (if k + 1 < n then S.levels (k + 1)
         else T.levels (j + (k + 1 - n)))
      rw [if_neg hkn, if_neg hnext]
      exact T.levels_strictMono (by omega)

/-- Every node of the finite retained prefix lies strictly below
the frontier's ambient level. -/
theorem initialPart_level_lt (S : StrongSubtree U)
    (n : ℕ) {z : U}
    (hz : z ∈ S.initialPart n) :
    U.level z < S.levels n := by
  obtain ⟨_, k, hkn, hlevel⟩ := hz
  rw [hlevel]
  exact S.levels_strictMono hkn

/-- Every node of the tail lies on or above the frontier's ambient
level. -/
theorem spliceTail_level_ge (S T : StrongSubtree U)
    (n : ℕ) {z : U}
    (hz : z ∈ S.spliceTail T n) :
    S.levels n ≤ U.level z := by
  obtain ⟨_, x, hx, hxz⟩ := hz
  calc
    S.levels n = U.level x := hx.2.symm
    _ ≤ U.level z := U.level_mono hxz

/-- At exactly the frontier ambient level, a tail node is equal
to its frontier ancestor. -/
theorem spliceTail_at_frontier (S T : StrongSubtree U)
    (n : ℕ) {z : U}
    (hz : z ∈ S.spliceTail T n)
    (hlevel : U.level z = S.levels n) :
    z ∈ S.sourceLevel n := by
  obtain ⟨_, x, hx, hxz⟩ := hz
  have hxzEq : x = z :=
    U.eq_of_le_of_level_eq hxz (hx.2.trans hlevel.symm)
  exact hxzEq ▸ hx

/-- The candidate graft agrees with S on every selected level
strictly below the frontier. -/
theorem spliceCarrier_level_before (S T : StrongSubtree U)
    {n k : ℕ} (hk : k < n) :
    {z : U | z ∈ S.spliceCarrier T n ∧
      U.level z = S.levels k} =
      S.sourceLevel k := by
  ext z
  constructor
  · rintro ⟨hz, hlevel⟩
    rcases hz with hprefix | htail
    · exact ⟨hprefix.1, hlevel⟩
    · have hge := S.spliceTail_level_ge T n htail
      have hlt := S.levels_strictMono hk
      rw [hlevel] at hge
      omega
  · intro hz
    refine ⟨Or.inl ?_, hz.2⟩
    exact ⟨hz.1, k, hk, hz.2⟩

/-- Provided the frontier of S is inside T, the candidate graft has
precisely that frontier on its first tail level. -/
theorem spliceCarrier_level_at (S T : StrongSubtree U)
    (n : ℕ)
    (htop : S.sourceLevel n ⊆ T.carrier) :
    {z : U | z ∈ S.spliceCarrier T n ∧
      U.level z = S.levels n} =
      S.sourceLevel n := by
  ext z
  constructor
  · rintro ⟨hz, hlevel⟩
    rcases hz with hprefix | htail
    · have hlt := S.initialPart_level_lt n hprefix
      rw [hlevel] at hlt
      exact (lt_irrefl _ hlt).elim
    · exact S.spliceTail_at_frontier T n htail hlevel
  · intro hz
    refine ⟨Or.inr ?_, hz.2⟩
    exact ⟨htop hz, z, hz, le_rfl⟩

/-- The prefix and the tail parts of the candidate graft are
disjoint, since they occupy disjoint ambient rank intervals. -/
theorem disjoint_initialPart_spliceTail
    (S T : StrongSubtree U) (n : ℕ) :
    Disjoint (S.initialPart n) (S.spliceTail T n) := by
  apply Set.disjoint_left.mpr
  intro z hzprefix hztail
  have hlt := S.initialPart_level_lt n hzprefix
  have hge := S.spliceTail_level_ge T n hztail
  omega

end StrongSubtree
end GeneralTree
end Milliken
