import Milliken.GeneralTree.HeterogeneousRestrictedReduction
import Milliken.GeneralTree.HeterogeneousReducedInduction

/-!
# Comparing ordinary and selected-level somewhere density

A full selected-level compression must preserve the *whole* frontier.
Before constructing its new ambient rooted tree, we verify the
obstruction translations on the original strongly branching trees.

Restricted somewhere-density always implies ordinary somewhere-density
for a strictly increasing selection. In the converse direction, an
ordinary witness can be moved to a *common* penultimate source level;
this proves the converse for the identity selection. It is important
that the original somewhere-dense definition permits different source
levels for the coordinates of its base tuple.

These lemmas prove the identity-case restricted reduction from the
checked heterogeneous reduced induction. For arbitrary sparse
selections, the missing implication genuinely requires full-frontier
compression; strong thinning cannot replace it.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Any selected-level somewhere-dense matrix is somewhere dense in
the ordinary (uncompressed) sense. The selected base has a common
source index, and strict monotonicity separates it from the target. -/
theorem heterogeneousRestrictedSomewhereDense_to_somewhereDense
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ) (hlevels : StrictMono levels)
    (M : HeterogeneousMatrix P)
    (hM : HeterogeneousRestrictedSomewhereDense P levels M) :
    M.SomewhereDense := by
  obtain ⟨p, q, hpq, base, hDense⟩ := hM
  refine ⟨base.1, levels q, ?_, hDense⟩
  intro i
  exact ⟨levels p, hlevels hpq, base.2 i⟩

/-- Every ordinary somewhere-dense matrix has a witness based on
one *common* source level. This uses finite positive dimension
only to show that the chosen target source level is positive.

When the source index selection is the identity, this is precisely
the restricted somewhere-dense property. -/
theorem heterogeneousSomewhereDense_to_restricted_id
    (P : Fin d → StrongSubtree U) (hd : 0 < d)
    (M : HeterogeneousMatrix P)
    (hM : M.SomewhereDense) :
    HeterogeneousRestrictedSomewhereDense P (fun n : ℕ => n) M := by
  classical
  obtain ⟨base, n, hbase, hDense⟩ := hM
  have hn : 0 < n := by
    obtain ⟨k, hk, _⟩ := hbase (⟨0, hd⟩ : Fin d)
    omega
  let p := n - 1
  have hpn : p < n := by
    dsimp [p]
    omega
  have hExt (i : Fin d) :
      ∃ z, z ∈ (P i).sourceLevel p ∧ base i ≤ z := by
    obtain ⟨k, hk, hbi⟩ := hbase i
    have hkp : k ≤ p := by
      dsimp [p]
      omega
    exact (P i).exists_sourceLevel_descendant hkp hbi
  let x : HeterogeneousLevelTuple P p :=
    ⟨fun i => Classical.choose (hExt i),
      fun i => (Classical.choose_spec (hExt i)).1⟩
  have hbx (i : Fin d) : base i ≤ x.1 i :=
    (Classical.choose_spec (hExt i)).2
  refine ⟨p, n, hpn, x, ?_⟩
  intro i z hz hxz
  exact hDense i z hz ((hbx i).trans hxz)

/-- For positive dimension, the two notions of somewhere density
agree at the identity source-index selection. -/
theorem heterogeneousSomewhereDense_iff_restricted_id
    (P : Fin d → StrongSubtree U) (hd : 0 < d)
    (M : HeterogeneousMatrix P) :
    M.SomewhereDense ↔
      HeterogeneousRestrictedSomewhereDense P
        (fun n : ℕ => n) M := by
  constructor
  · exact heterogeneousSomewhereDense_to_restricted_id P hd M
  · exact heterogeneousRestrictedSomewhereDense_to_somewhereDense
      P (fun n : ℕ => n) (strictMono_id) M

/-- Negative ordinary somewhere-density follows from the selected
obstruction at the identity subsequence. -/
theorem heterogeneousNoSomewhereDense_of_noRestricted_id
    (P : Fin d → StrongSubtree U) (hd : 0 < d)
    (Q : Set (Fin d → U))
    (hno : ¬ HeterogeneousContainsRestrictedSomewhereDense
      P (fun n : ℕ => n) Qᶜ) :
    ¬ HeterogeneousContainsSomewhereDense P Qᶜ := by
  rintro ⟨M, hM, hSub⟩
  exact hno ⟨M,
    heterogeneousSomewhereDense_to_restricted_id P hd M hM, hSub⟩

/-- A checked identity-selection instance of the restricted reduced
dichotomy. It uses only previous-dimensional heterogeneous HDHL,
the common source-level synchronization and the existing checked
reduced induction. The sparse-selection case needs the actual
compressed ambient tree, not this identity argument. -/
theorem heterogeneousRestrictedReduced_id_of_previous
    (P : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d) (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R) :
    HeterogeneousRestrictedReducedDichotomy
      P (fun n : ℕ => n) := by
  intro Q hno
  exact heterogeneousReducedHDHL_of_previous P hd L hP hAll Q
    (heterogeneousNoSomewhereDense_of_noRestricted_id
      P (Nat.zero_lt_succ d) Q hno)

end GeneralTree
end Milliken
