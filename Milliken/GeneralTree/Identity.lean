import Milliken.GeneralTree.OrderLemmas

/-!
# The whole ambient tree is an infinite strong subtree

This constructs the canonical point of Todorčević's space S∞(U)
for every pruned, locally finitely branching rooted ambient tree U.
Its selected levels are precisely the ambient levels and its carrier
is all of U. In particular S∞(U) is nonempty without choosing a
global finite branching alphabet.

The proof uses the ambient rank laws in AmbientTree.lean, proved from
the rooted tree's predecessor order.
-/

namespace Milliken
namespace GeneralTree

/-- The identity infinite strong subtree of an arbitrary ambient tree. -/
def identityStrongSubtree (U : AmbientTree) : StrongSubtree U where
  carrier := Set.univ
  levels := fun n => n
  levels_strictMono := strictMono_id
  root := ⊥
  root_mem := Set.mem_univ _
  root_level := U.level_root
  root_below := by
    intro x hx
    exact bot_le
  carrier_levels := by
    intro x hx
    exact ⟨U.level x, rfl⟩
  predecessor_exists := by
    intro n z hz hlevel
    have hzne : z ≠ (⊥ : U) := by
      intro heq
      rw [heq, U.level_root] at hlevel
      omega
    have hcov : Order.pred z ⋖ z :=
      Order.pred_covBy_of_not_isMin
        ((not_isMin_iff_ne_bot).mpr hzne)
    refine ⟨Order.pred z, Set.mem_univ _, ?_, hcov.le⟩
    have hstep := U.level_covBy hcov
    omega
  successor_unique := by
    intro n x hx hlevel y hxy
    refine ⟨y, ⟨Set.mem_univ _, ?_, le_rfl⟩, ?_⟩
    · have hstep := U.level_covBy hxy
      omega
    · intro z hz
      have hstep := U.level_covBy hxy
      have hzlevel := hz.2.1
      have heq : U.level y = U.level z := by omega
      exact (U.eq_of_le_of_level_eq hz.2.2 heq).symm

/-- The space of infinite strong subtrees is nonempty for every ambient
tree satisfying the published hypotheses. -/
theorem sinfinity_nonempty (U : AmbientTree) :
    Nonempty (SInfinity U) :=
  ⟨identityStrongSubtree U⟩

/-- The canonical identity point uses every ambient level and node. -/
@[simp] theorem identityStrongSubtree_carrier (U : AmbientTree) :
    (identityStrongSubtree U).carrier = Set.univ := rfl

@[simp] theorem identityStrongSubtree_levels (U : AmbientTree) (n : ℕ) :
    (identityStrongSubtree U).levels n = n := rfl

end GeneralTree
end Milliken
