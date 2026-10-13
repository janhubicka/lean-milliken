import Milliken.GeneralTree.HeterogeneousWedgeOrder

/-!
# Predecessor and finite parent chains on a finite forest with a common root

The parent of a component root is the new global root; all other
parents are exactly those in their original component. The resulting
WedgeNode is a Mathlib PredOrder. A rank equal to 1 plus the
coordinate's original height proves that strict predecessor chains
cannot be infinite; Mathlib's well-founded-predecessor theorem then
yields IsPredArchimedean.

This proves a RootedTree structure on a finite dependent forest.
It does not yet claim finite branching or no terminal nodes; those
are handled separately when constructing the full AmbientTree.
-/

namespace Milliken
namespace GeneralTree

variable {d : ℕ}

namespace WedgeNode

variable (T : Fin d → AmbientTree)

/-- The immediate parent in the common-root wedge. -/
noncomputable def parent (z : WedgeNode T) : WedgeNode T := by
  classical
  exact match z with
    | none => ⊥
    | some ⟨i, x⟩ =>
        if x = (⊥ : T i) then ⊥
        else embed T i (Order.pred x)

@[simp] theorem parent_bot :
    parent T (⊥ : WedgeNode T) = ⊥ := by
  classical
  rfl

@[simp] theorem parent_embed_root (i : Fin d) :
    parent T (embed T i (⊥ : T i)) = ⊥ := by
  classical
  simp [parent, embed]

@[simp] theorem parent_embed_nonroot
    (i : Fin d) (x : T i) (hx : x ≠ ⊥) :
    parent T (embed T i x) =
      embed T i (Order.pred x) := by
  classical
  simp [parent, embed, hx]

/-- Actual original parents define a PredOrder on the glued forest. -/
noncomputable instance predOrder : PredOrder (WedgeNode T) where
  pred := parent T
  pred_le := by
    intro z
    rcases z with _ | ⟨i, x⟩
    · exact le_rfl
    change parent T (embed T i x) ≤ embed T i x
    by_cases hx : x = ⊥
    · subst x
      rw [parent_embed_root]
      exact bot_le
    · rw [parent_embed_nonroot T i x hx]
      exact (embed_le_embed_iff T i (Order.pred x) x).mpr
        (Order.pred_le x)
  min_of_le_pred := by
    intro z hz
    rcases z with _ | ⟨i, x⟩
    · exact isMin_bot
    change embed T i x ≤ parent T (embed T i x) at hz
    by_cases hx : x = ⊥
    · subst x
      rw [parent_embed_root] at hz
      exact False.elim (WithBot.not_coe_le_bot _ hz)
    · rw [parent_embed_nonroot T i x hx] at hz
      have hxe : x ≤ Order.pred x :=
        (embed_le_embed_iff T i x (Order.pred x)).mp hz
      have hmin : IsMin x := Order.min_of_le_pred hxe
      exact False.elim ((not_isMin_iff_ne_bot).mpr hx hmin)
  le_pred_of_lt := by
    intro z w hzw
    rcases z with _ | ⟨i, x⟩
    · exact bot_le
    rcases w with _ | ⟨j, y⟩
    · exact False.elim ((not_lt_of_ge bot_le) hzw)
    change embed T i x < embed T j y at hzw
    have hij : i = j :=
      (Sigma.le_def.mp
        (WithBot.coe_le_coe.mp hzw.le)).1
    subst j
    have hxy : x < y := by
      have hle : x ≤ y :=
        (embed_le_embed_iff T i x y).mp hzw.le
      have hne : x ≠ y := by
        intro heq
        apply hzw.ne
        rw [heq]
      exact lt_of_le_of_ne hle hne
    have hyne : y ≠ (⊥ : T i) := by
      intro heq
      subst y
      exact (not_lt_of_ge bot_le) hxy
    change embed T i x ≤ parent T (embed T i y)
    rw [parent_embed_nonroot T i y hyne]
    exact (embed_le_embed_iff T i x (Order.pred y)).mpr
      (Order.le_pred_of_lt hxy)

/-- Rank above the new common root; component height is shifted
by one, ensuring all component roots have rank one. -/
noncomputable def rank : WedgeNode T → ℕ
  | none => 0
  | some ⟨i, x⟩ => (T i).level x + 1

@[simp] theorem rank_bot :
    rank T (⊥ : WedgeNode T) = 0 := rfl

@[simp] theorem rank_embed (i : Fin d) (x : T i) :
    rank T (embed T i x) = (T i).level x + 1 := rfl

@[simp] theorem rank_embed_root (i : Fin d) :
    rank T (embed T i (⊥ : T i)) = 1 := by
  simp [rank_embed, AmbientTree.level_root]

/-- The rank increases strictly along every strict wedge ancestor,
also for locally unbounded degrees and unrelated coordinates. -/
theorem rank_lt_of_lt {a b : WedgeNode T}
    (hab : a < b) : rank T a < rank T b := by
  rcases a with _ | ⟨i, x⟩
  · rcases b with _ | ⟨j, y⟩
    · exact False.elim ((lt_irrefl _) hab)
    · change (0 : ℕ) < (T j).level y + 1
      omega
  · rcases b with _ | ⟨j, y⟩
    · exact False.elim ((not_lt_of_ge bot_le) hab)
    · have hs : embed T i x < embed T j y := by
        change embed T i x < embed T j y at hab
        exact hab
      have hij : i = j :=
        (Sigma.le_def.mp
          (WithBot.coe_le_coe.mp hs.le)).1
      subst j
      have hxy : x < y := by
        have hle : x ≤ y :=
          (embed_le_embed_iff T i x y).mp hs.le
        have hne : x ≠ y := by
          intro heq
          apply hs.ne
          rw [heq]
        exact lt_of_le_of_ne hle hne
      have hlev : (T i).level x < (T i).level y :=
        (T i).level_lt hxy
      change (T i).level x + 1 < (T i).level y + 1
      omega

/-- All strictly descending chains in a wedge are finite, since
their natural-valued ranks decrease strictly. -/
noncomputable instance wellFoundedLT : WellFoundedLT (WedgeNode T) :=
  Subrelation.wf
    (fun h => rank_lt_of_lt T h)
    (measure (rank T)).2

/-- The generic well-founded predecessor theorem supplies
IsPredArchimedean. Together with the wedge meet and bottom, these
are the exact four Mathlib instances for RootedTree. -/
noncomputable def rootedTree : RootedTree where
  α := WedgeNode T

end WedgeNode
end GeneralTree
end Milliken
