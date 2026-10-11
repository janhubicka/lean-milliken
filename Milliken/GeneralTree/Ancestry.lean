import Milliken.GeneralTree.PrefixFinitization

/-!
# Selected-level ancestry for general-tree amalgamation

The chosen strong-tree root is its only node on source level zero.
The `predecessor_exists` field of the published strong-tree
representation supplies an ancestor on every earlier selected source
level. Thus any node past a finite stem lies above a node on its
top frontier. This prepares the graft/splice needed for A.3.

No uniform bound on the ambient branching degree is used. These
lemmas do not claim A.3 or the general Milliken theorem.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A strong subtree has just one node on selected source level zero. -/
theorem sourceLevel_zero_eq_singleton (S : StrongSubtree U) :
    S.sourceLevel 0 = {S.root} := by
  ext x
  constructor
  · intro hx
    have hroot : S.root = x :=
      U.eq_of_le_of_level_eq
        (S.root_below x hx.1)
        (S.root_level.trans hx.2.symm)
    exact hroot.symm
  · intro hx
    have heq : x = S.root := hx
    subst x
    exact ⟨S.root_mem, S.root_level⟩

/-- Every node on a later selected level has a retained ancestor
on every earlier selected level. The existence assertion is enough
for the A.3 frontier decomposition. -/
theorem exists_sourceLevel_ancestor
    (S : StrongSubtree U)
    {n m : ℕ} (hnm : n ≤ m)
    {z : U} (hz : z ∈ S.sourceLevel m) :
    ∃ x : U, x ∈ S.sourceLevel n ∧ x ≤ z := by
  induction m, hnm using Nat.le_induction generalizing z with
  | base =>
      exact ⟨z, hz, le_rfl⟩
  | succ m hnm ih =>
      obtain ⟨p, hp, hpl, hpz⟩ :=
        S.predecessor_exists m z hz.1 hz.2
      obtain ⟨x, hx, hxp⟩ := ih (z := p) ⟨hp, hpl⟩
      exact ⟨x, hx, hxp.trans hpz⟩

/-- Any node outside the first n source levels is above a node of
the n-th source level, the natural boundary for stem/tail splicing. -/
theorem exists_frontier_ancestor
    (S : StrongSubtree U) (n : ℕ)
    {z : U} (hz : z ∈ S.carrier)
    (hout : z ∉ S.initialPart n) :
    ∃ x : U, x ∈ S.sourceLevel n ∧ x ≤ z := by
  obtain ⟨m, hm⟩ := S.carrier_levels z hz
  have hnm : n ≤ m := by
    by_contra hn
    have hmn : m < n := Nat.lt_of_not_ge hn
    exact hout ⟨hz, m, hmn, hm⟩
  exact S.exists_sourceLevel_ancestor hnm ⟨hz, hm⟩

end StrongSubtree
end GeneralTree
end Milliken
