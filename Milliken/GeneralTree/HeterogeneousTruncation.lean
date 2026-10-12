import Milliken.GeneralTree.HeterogeneousRefinement
import Milliken.GeneralTree.FrontierUniqueness

/-!
# Heterogeneous level-vector truncation at selected source levels

Todorčević's stabilization and section-fusion arguments truncate
the first d coordinates to a prescribed earlier level. In arbitrary
pruned locally finitely branching trees there is no literal
`List.take`; instead each node has a unique retained ancestor
at each preceding *selected source level*.

We define the source-ancestor operation and its coordinatewise
product. If one level vector lies coordinatewise below another,
their truncations at an earlier common source index agree.
These facts require no fixed finite alphabet or uniform branching bound.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

namespace StrongSubtree

/-- The uniquely determined retained ancestor of z on selected
source level q. -/
noncomputable def sourceAncestorAt
    (S : StrongSubtree U)
    {q m : ℕ} (hqm : q ≤ m)
    {z : U} (hz : z ∈ S.sourceLevel m) : U :=
  Classical.choose (S.existsUnique_sourceLevel_ancestor hqm hz)

/-- The canonical earlier source-level ancestor is retained
and lies below the original node. -/
theorem sourceAncestorAt_spec
    (S : StrongSubtree U)
    {q m : ℕ} (hqm : q ≤ m)
    {z : U} (hz : z ∈ S.sourceLevel m) :
    S.sourceAncestorAt hqm hz ∈ S.sourceLevel q ∧
      S.sourceAncestorAt hqm hz ≤ z :=
  (Classical.choose_spec (S.existsUnique_sourceLevel_ancestor hqm hz)).1

/-- Truncating an ancestor and its descendant to the same earlier
source level gives the same retained node. -/
theorem sourceAncestorAt_eq_of_le
    (S : StrongSubtree U)
    {q l m : ℕ} (hql : q ≤ l) (hlm : l ≤ m)
    {x z : U} (hx : x ∈ S.sourceLevel l)
    (hz : z ∈ S.sourceLevel m) (hxz : x ≤ z) :
    S.sourceAncestorAt hql hx =
      S.sourceAncestorAt (hql.trans hlm) hz := by
  let a := S.sourceAncestorAt hql hx
  let b := S.sourceAncestorAt (hql.trans hlm) hz
  have ha : a ∈ S.sourceLevel q ∧ a ≤ x :=
    S.sourceAncestorAt_spec hql hx
  have hb : b ∈ S.sourceLevel q ∧ b ≤ z :=
    S.sourceAncestorAt_spec (hql.trans hlm) hz
  have haz : a ≤ z := ha.2.trans hxz
  have hrank : U.level a = U.level b :=
    ha.1.2.trans hb.1.2.symm
  rcases le_total_of_directed haz hb.2 with hba | hab
  · exact (U.eq_of_le_of_level_eq hba hrank.symm).symm
  · exact U.eq_of_le_of_level_eq hab hrank

end StrongSubtree

/-- Coordinatewise truncation of a level vector to a lower
selected source index, using the actual rooted-tree ancestors. -/
noncomputable def heterogeneousTruncate
    (P : Fin d → StrongSubtree U)
    {q m : ℕ} (hqm : q ≤ m)
    (x : HeterogeneousLevelTuple P m) :
    HeterogeneousLevelTuple P q :=
  ⟨fun i => (P i).sourceAncestorAt hqm (x.2 i),
    fun i => ((P i).sourceAncestorAt_spec hqm (x.2 i)).1⟩

/-- The truncated vector lies coordinatewise below its input. -/
theorem heterogeneousTruncate_le
    (P : Fin d → StrongSubtree U)
    {q m : ℕ} (hqm : q ≤ m)
    (x : HeterogeneousLevelTuple P m) :
    ∀ i, (heterogeneousTruncate P hqm x).1 i ≤ x.1 i := by
  intro i
  exact ((P i).sourceAncestorAt_spec hqm (x.2 i)).2

/-- Source truncation commutes with coordinatewise extensions:
any two comparable level vectors have the same truncation to
a source index preceding both of their levels. -/
theorem heterogeneousTruncate_eq_of_le
    (P : Fin d → StrongSubtree U)
    {q l m : ℕ} (hql : q ≤ l) (hlm : l ≤ m)
    (x : HeterogeneousLevelTuple P l)
    (z : HeterogeneousLevelTuple P m)
    (hxz : ∀ i, x.1 i ≤ z.1 i) :
    heterogeneousTruncate P hql x =
      heterogeneousTruncate P (hql.trans hlm) z := by
  apply Subtype.ext
  funext i
  exact (P i).sourceAncestorAt_eq_of_le
    hql hlm (x.2 i) (z.2 i) (hxz i)

end GeneralTree
end Milliken
