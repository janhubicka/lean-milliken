import Milliken.GeneralTree.HeterogeneousWedgeAmbient

/-!
# Exact heights of the common-root heterogeneous forest

The natural rank used to establish local finiteness is precisely
Mathlib's AmbientTree.level for the new wedge. Therefore the
component indexed by i occupies ambient levels 1,2,... in the
wedge, with its original level n shifted to n+1.

This is the synchronization lemma required when each component
of a heterogeneous compressed family is to become a strong subtree
of one common ambient. All statements are geometric and do not use
Halpern–Läuchli or Milliken.
-/

namespace Milliken
namespace GeneralTree

variable {d : ℕ}

namespace WedgeNode

variable (T : Fin d → AmbientTree)

/-- Rank zero is exactly the new global root. -/
theorem rank_eq_zero_iff (z : WedgeNode T) :
    rank T z = 0 ↔ z = ⊥ := by
  rcases z with _ | ⟨i, x⟩
  · simp
  · change rank T (embed T i x) = 0 ↔
      (embed T i x) = (⊥ : WedgeNode T)
    simp

/-- New ambient height equals one plus coordinate height, or zero
at the added root. This is proved by induction on the actual rank
and the checked cover/parent structure. -/
theorem ambient_level_eq_rank (hd : 0 < d) (z : WedgeNode T) :
    (ambientTree T hd).level z = rank T z := by
  have aux :
      ∀ (n : ℕ) (x : WedgeNode T), rank T x = n →
        (ambientTree T hd).level x = n := by
    intro n
    induction n with
    | zero =>
        intro x hx
        have hroot : x = ⊥ :=
          (rank_eq_zero_iff T x).mp hx
        rw [hroot]
        exact (ambientTree T hd).level_root
    | succ n ih =>
        intro x hx
        have hxne : x ≠ ⊥ := by
          intro hroot
          apply (rank_eq_zero_iff T x).mpr at hroot
          omega
        have hparent :
            rank T (parent T x) = n := by
          have hs := rank_parent_succ_of_ne_bot T hxne
          omega
        have hcov : parent T x ⋖ x :=
          Order.pred_covBy_of_not_isMin
            ((not_isMin_iff_ne_bot).mpr hxne)
        have hlevel :
            (ambientTree T hd).level x =
              (ambientTree T hd).level (parent T x) + 1 :=
          (ambientTree T hd).level_covBy hcov
        have hp := ih (parent T x) hparent
        omega
  exact aux (rank T z) z rfl

/-- The level of a node from component i is its former ambient
level plus exactly one. -/
theorem ambient_level_embed (hd : 0 < d)
    (i : Fin d) (x : T i) :
    (ambientTree T hd).level (embed T i x) =
      (T i).level x + 1 := by
  calc
    (ambientTree T hd).level (embed T i x) =
        rank T (embed T i x) :=
      ambient_level_eq_rank T hd _
    _ = (T i).level x + 1 := rank_embed T i x

/-- The complete common-root ambient level n+1 consists precisely
of all tagged coordinate nodes whose original level is n. -/
theorem ambient_levelSet_succ (hd : 0 < d) (n : ℕ) :
    (ambientTree T hd).levelSet (n + 1) =
      ⋃ i : Fin d, (embed T i) '' (T i).levelSet n := by
  classical
  ext z
  constructor
  · intro hz
    rcases z with _ | ⟨i, x⟩
    · have hb : (ambientTree T hd).level
          (⊥ : WedgeNode T) = 0 :=
        (ambientTree T hd).level_root
      change (ambientTree T hd).level
        (⊥ : WedgeNode T) = n + 1 at hz
      omega
    · have hx : (T i).level x = n := by
        change (ambientTree T hd).level (embed T i x) =
          n + 1 at hz
        rw [ambient_level_embed] at hz
        omega
      exact Set.mem_iUnion.mpr
        ⟨i, Set.mem_image_of_mem (embed T i) hx⟩
  · intro hz
    obtain ⟨i, x, hx, rfl⟩ := Set.mem_iUnion.mp hz
    change (ambientTree T hd).level (embed T i x) = n + 1
    rw [ambient_level_embed]
    change (T i).level x = n at hx
    omega

end WedgeNode
end GeneralTree
end Milliken
