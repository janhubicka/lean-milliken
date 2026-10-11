import Milliken.GeneralTree.SpliceLevels

/-!
# Cone order and predecessor transport for general strong-tree grafting

In a rooted tree, two ancestors of one node are comparable. If the
ambient rank of the first does not exceed that of the second, the
first lies below the second. This elementary order fact is exactly
what is needed to show that the selected predecessor of a graft-tail
node stays inside the same chosen frontier cone.

The argument is independent of the branching degrees and does not
use a global alphabet. It is the missing predecessor-closure component
of the candidate A.3 graft, not yet the full strongness theorem.
-/

namespace Milliken

namespace AmbientTree

/-- If x and y have a common descendant z, and the ambient rank
of x does not exceed that of y, then x is an ancestor of y.
This is the chain property of the predecessor set of z. -/
theorem le_of_common_descendant_of_level_le
    (U : AmbientTree)
    {x y z : U}
    (hx : x ≤ z) (hy : y ≤ z)
    (hlevel : U.level x ≤ U.level y) :
    x ≤ y := by
  rcases le_total_of_directed hx hy with hyx | hxy
  · have hrank : U.level y ≤ U.level x :=
      U.level_mono hyx
    have heq : U.level y = U.level x :=
      le_antisymm hrank hlevel
    have hnodes : y = x :=
      U.eq_of_le_of_level_eq hyx heq
    rw [hnodes]
  · exact hxy

end AmbientTree

namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- If a T-ancestor p of a graft-tail node z lies on or
above T's selected frontier level j, then p belongs to the
same chosen frontier cone. This is the central tail
predecessor-closure law for the relative graft. -/
theorem spliceTail_ancestor
    (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j)
    {z p : U}
    (hz : z ∈ S.spliceTail T n)
    (hp : p ∈ T.carrier)
    (hpz : p ≤ z)
    (hplevel : T.levels j ≤ U.level p) :
    p ∈ S.spliceTail T n := by
  obtain ⟨_, x, hx, hxz⟩ := hz
  have hxplevel : U.level x ≤ U.level p := by
    calc
      U.level x = S.levels n := hx.2
      _ = T.levels j := hlevel
      _ ≤ U.level p := hplevel
  have hxp : x ≤ p :=
    U.le_of_common_descendant_of_level_le hxz hpz hxplevel
  exact ⟨hp, x, hx, hxp⟩

/-- Nodes on a selected source level before the splice cut are
exactly the corresponding nodes of the original finite stem. -/
theorem splice_source_before
    (S T : StrongSubtree U)
    {n j k : ℕ} (hk : k < n)
    {z : U}
    (hz : z ∈ S.spliceCarrier T n)
    (hzlevel :
      U.level z = S.spliceLevels T n j k) :
    z ∈ S.sourceLevel k := by
  have hlevel : U.level z = S.levels k := by
    rw [S.spliceLevels_before T hk] at hzlevel
    exact hzlevel
  have hmem :
      z ∈ {w : U |
        w ∈ S.spliceCarrier T n ∧ U.level w = S.levels k} :=
    ⟨hz, hlevel⟩
  rw [S.spliceCarrier_level_before T hk] at hmem
  exact hmem

/-- At the frontier cut, the selected source nodes of the candidate
are exactly the retained frontier nodes of S. -/
theorem splice_source_at
    (S T : StrongSubtree U)
    (n j : ℕ)
    (hlevel : S.levels n = T.levels j)
    (htop : S.sourceLevel n ⊆ T.carrier)
    {z : U}
    (hz : z ∈ S.spliceCarrier T n)
    (hzlevel :
      U.level z = S.spliceLevels T n j n) :
    z ∈ S.sourceLevel n := by
  have hlev : S.spliceLevels T n j n = S.levels n := by
    change (if n < n then S.levels n
      else T.levels (j + (n - n))) = S.levels n
    simp [hlevel]
  have hzlev : U.level z = S.levels n :=
    hzlevel.trans hlev
  have hmem :
      z ∈ {w : U |
        w ∈ S.spliceCarrier T n ∧ U.level w = S.levels n} :=
    ⟨hz, hzlev⟩
  rw [S.spliceCarrier_level_at T n htop] at hmem
  exact hmem

/-- All nodes on selected tail levels belong to T and descend
from some selected S-frontier node; this is the source form used
to transfer T's successor-uniqueness law to the graft. -/
theorem splice_source_after
    (S T : StrongSubtree U)
    (n j k : ℕ)
    (hlevel : S.levels n = T.levels j)
    {z : U}
    (hz : z ∈ S.spliceCarrier T n)
    (hzlevel :
      U.level z = S.spliceLevels T n j (n + k)) :
    z ∈ T.sourceLevel (j + k) ∧
      ∃ x : U, x ∈ S.sourceLevel n ∧ x ≤ z := by
  have hmem :
      z ∈ {w : U |
        w ∈ S.spliceCarrier T n ∧
          U.level w = S.spliceLevels T n j (n + k)} :=
    ⟨hz, hzlevel⟩
  rw [S.spliceCarrier_level_tail T n j k hlevel] at hmem
  exact hmem

end StrongSubtree
end GeneralTree
end Milliken
