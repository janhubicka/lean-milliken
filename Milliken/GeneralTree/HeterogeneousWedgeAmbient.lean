import Milliken.GeneralTree.HeterogeneousWedgePred

/-!
# A common pruned locally finite ambient tree for a heterogeneous forest

For a *positive* finite number of arbitrary pruned, finitely
branching rooted coordinate trees, adjoining one new common root
produces another AmbientTree. The new root has exactly one direct
child per coordinate, and all further branching agrees with the
respective component.

The proof uses the natural rank of the wedge, equal to one plus the
coordinate's ambient height. Every full rank level is a finite
union of finite coordinate levels. Cover relations increase rank
exactly by one, so local finiteness of rank levels implies local
finiteness of successor sets. No globally bounded degree exists
or is required.
-/

namespace Milliken
namespace GeneralTree

variable {d : ℕ}

namespace WedgeNode

variable (T : Fin d → AmbientTree)

/-- Every non-root node has rank exactly one more than its
parent, including coordinate roots whose parent is the new root. -/
theorem rank_parent_succ_of_ne_bot
    {z : WedgeNode T} (hz : z ≠ ⊥) :
    rank T z = rank T (parent T z) + 1 := by
  rcases z with _ | ⟨i, x⟩
  · exact (hz rfl).elim
  change rank T (embed T i x) =
    rank T (parent T (embed T i x)) + 1
  by_cases hx : x = ⊥
  · subst x
    simp
  · have hnotMin : ¬ IsMin x :=
      (not_isMin_iff_ne_bot).mpr hx
    have hcov : Order.pred x ⋖ x :=
      Order.pred_covBy_of_not_isMin hnotMin
    have hlev := (T i).level_covBy hcov
    simp only [parent_embed_nonroot T i x hx, rank_embed]
    omega

/-- Cover relations increase the new wedge rank by exactly one. -/
theorem rank_covBy {x y : WedgeNode T}
    (hxy : x ⋖ y) :
    rank T y = rank T x + 1 := by
  have hy : y ≠ ⊥ := by
    intro heq
    subst y
    exact (not_lt_of_ge bot_le) hxy.lt
  have hp : parent T y = x := Order.pred_eq_of_covBy hxy
  have h := rank_parent_succ_of_ne_bot T hy
  rw [hp] at h
  exact h

/-- Every complete wedge level is finite, with locally arbitrary
degrees in the component trees. -/
theorem rank_level_finite (n : ℕ) :
    ({x : WedgeNode T | rank T x = n} :
      Set (WedgeNode T)).Finite := by
  classical
  cases n with
  | zero =>
      apply (Set.finite_singleton (⊥ : WedgeNode T)).subset
      intro z hz
      have hbot : z = (⊥ : WedgeNode T) := by
        rcases z with _ | ⟨i, x⟩
        · rfl
        · change rank T (embed T i x) = 0 at hz
          simp only [rank_embed] at hz
          omega
      simpa only [Set.mem_singleton_iff] using hbot
  | succ n =>
      let C : Set (WedgeNode T) :=
        ⋃ i : Fin d, (embed T i) '' (T i).levelSet n
      have hC : C.Finite := by
        dsimp [C]
        exact Set.finite_iUnion
          (fun i => ((T i).levelSet_finite n).image (embed T i))
      apply hC.subset
      intro z hz
      rcases z with _ | ⟨i, x⟩
      · change rank T (⊥ : WedgeNode T) = n + 1 at hz
        rw [rank_bot] at hz
        omega
      · have hx : (T i).level x = n := by
          change rank T (embed T i x) = n + 1 at hz
          rw [rank_embed] at hz
          omega
        exact Set.mem_iUnion.mpr
          ⟨i, Set.mem_image_of_mem (embed T i) hx⟩

/-- Local finiteness of wedge children follows from finiteness
of the next rank level, not from a global bound on degree. -/
theorem children_finite (x : WedgeNode T) :
    ({y : WedgeNode T | x ⋖ y} :
      Set (WedgeNode T)).Finite := by
  apply (rank_level_finite T (rank T x + 1)).subset
  intro y hy
  exact rank_covBy T hy

/-- The new root has at least one child if the dimension is
positive; each other wedge node has a child in its original tree. -/
theorem has_child (hd : 0 < d) (x : WedgeNode T) :
    ∃ y : WedgeNode T, x ⋖ y := by
  classical
  rcases x with _ | ⟨i, x⟩
  · let i : Fin d := ⟨0, hd⟩
    refine ⟨embed T i (⊥ : T i), ?_⟩
    have hne : embed T i (⊥ : T i) ≠ ⊥ :=
      WithBot.coe_ne_bot
    have hmin : ¬ IsMin (embed T i (⊥ : T i)) :=
      (not_isMin_iff_ne_bot).mpr hne
    have hc : Order.pred (embed T i (⊥ : T i)) ⋖
        embed T i (⊥ : T i) :=
      Order.pred_covBy_of_not_isMin hmin
    change parent T (embed T i (⊥ : T i)) ⋖
      embed T i (⊥ : T i) at hc
    rw [parent_embed_root] at hc
    exact hc
  · change ∃ y : WedgeNode T, embed T i x ⋖ y
    obtain ⟨y, hxy⟩ := (T i).has_child x
    have hyne : y ≠ (⊥ : T i) := by
      intro heq
      subst y
      exact (not_lt_of_ge bot_le) hxy.lt
    have hne : embed T i y ≠ ⊥ :=
      WithBot.coe_ne_bot
    have hmin : ¬ IsMin (embed T i y) :=
      (not_isMin_iff_ne_bot).mpr hne
    have hparent :
        parent T (embed T i y) = embed T i x := by
      rw [parent_embed_nonroot T i y hyne]
      rw [Order.pred_eq_of_covBy hxy]
    have hcov : Order.pred (embed T i y) ⋖ embed T i y :=
      Order.pred_covBy_of_not_isMin hmin
    refine ⟨embed T i y, ?_⟩
    change parent T (embed T i y) ⋖ embed T i y at hcov
    rw [hparent] at hcov
    exact hcov

/-- The finite forest with a shared root is a real AmbientTree.
Only positivity of the number of components is required. -/
noncomputable def ambientTree (hd : 0 < d) : AmbientTree where
  toRootedTree := rootedTree T
  finite_children := children_finite T
  has_child := has_child T hd

end WedgeNode
end GeneralTree
end Milliken
