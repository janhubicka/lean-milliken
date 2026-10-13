import Milliken.GeneralTree.CompressedSourceRank

/-!
# A single rooted order for a finite forest of heterogeneous trees

The node type is a new bottom element together with a dependent
disjoint union of the original coordinate tree nodes. Within a fibre
the order is its genuine ancestor order; different fibres have no
common ancestor except the new root.

The construction works for arbitrary finitely many non-isomorphic,
pruned, locally finite ambient trees. In particular, no common
branching alphabet or global degree bound is introduced.
-/

namespace Milliken
namespace GeneralTree

variable {d : ℕ}

/-- A forest of arbitrary rooted trees, with one *new* common root.
The default Sigma order is disjoint within fibres, and WithBot
introduces the common root below them all. -/
abbrev WedgeNode (T : Fin d → AmbientTree) :=
  WithBot (Σ i : Fin d, T i)

namespace WedgeNode

variable (T : Fin d → AmbientTree)

/-- Include one coordinate node as a node of the common forest. -/
def embed (i : Fin d) (z : T i) : WedgeNode T :=
  (⟨i, z⟩ : Σ j : Fin d, T j)

/-- Inclusion reflects and preserves the exact ancestor order. -/
@[simp] theorem embed_le_embed_iff (i : Fin d) (x y : T i) :
    embed T i x ≤ embed T i y ↔ x ≤ y := by
  exact WithBot.coe_le_coe.trans Sigma.mk_le_mk_iff

/-- Distinct components have incomparable non-root nodes. -/
theorem embed_not_le_of_ne
    {i j : Fin d} (hij : i ≠ j)
    (x : T i) (y : T j) :
    ¬ embed T i x ≤ embed T j y := by
  intro h
  have h' := (Sigma.le_def.mp
    (WithBot.coe_le_coe.mp h)).1
  exact hij h'

/-- Greatest common ancestor of two tagged nodes, or the new
root when their tags differ. All fibrewise meets are inherited from
their actual rooted-tree orders. -/
noncomputable def meet : WedgeNode T → WedgeNode T → WedgeNode T
  | (some ⟨i, x⟩), (some ⟨j, y⟩) =>
      if h : j = i then
        (⟨i, x ⊓ (h ▸ y)⟩ : Σ k : Fin d, T k)
      else ⊥
  | _, _ => ⊥

@[simp] theorem meet_embed_same (i : Fin d) (x y : T i) :
    meet T (embed T i x) (embed T i y) =
      embed T i (x ⊓ y) := by
  classical
  simp [meet, embed]

@[simp] theorem meet_embed_diff
    {i j : Fin d} (hij : i ≠ j)
    (x : T i) (y : T j) :
    meet T (embed T i x) (embed T j y) = ⊥ := by
  classical
  simp [meet, embed, Ne.symm hij]

/-- The fresh bottom and genuine fibrewise meets form a
semilattice. The order is the default WithBot/Sigma ancestor order,
not a fabricated lexicographic order. -/
noncomputable instance semilatticeInf : SemilatticeInf (WedgeNode T) where
  inf := meet T
  inf_le_left := by
    intro a b
    rcases a with _ | ⟨i, x⟩
    · exact bot_le
    rcases b with _ | ⟨j, y⟩
    · exact bot_le
    by_cases hij : i = j
    · subst j
      simpa only [meet_embed_same, embed_le_embed_iff] using
        (inf_le_left : x ⊓ y ≤ x)
    · have hji : j ≠ i := Ne.symm hij
      rw [meet_embed_diff T hji]
      exact bot_le
  inf_le_right := by
    intro a b
    rcases a with _ | ⟨i, x⟩
    · exact bot_le
    rcases b with _ | ⟨j, y⟩
    · exact bot_le
    by_cases hij : i = j
    · subst j
      simpa only [meet_embed_same, embed_le_embed_iff] using
        (inf_le_right : x ⊓ y ≤ y)
    · have hji : j ≠ i := Ne.symm hij
      rw [meet_embed_diff T hji]
      exact bot_le
  le_inf := by
    intro z a b hza hzb
    rcases z with _ | ⟨i, z⟩
    · exact bot_le
    rcases a with _ | ⟨j, x⟩
    · exact False.elim (WithBot.not_coe_le_bot _ hza)
    rcases b with _ | ⟨k, y⟩
    · exact False.elim (WithBot.not_coe_le_bot _ hzb)
    have hij : i = j :=
      (Sigma.le_def.mp (WithBot.coe_le_coe.mp hza)).1
    have hik : i = k :=
      (Sigma.le_def.mp (WithBot.coe_le_coe.mp hzb)).1
    subst j
    subst k
    have hzx : z ≤ x := Sigma.mk_le_mk_iff.mp
      (WithBot.coe_le_coe.mp hza)
    have hzy : z ≤ y := Sigma.mk_le_mk_iff.mp
      (WithBot.coe_le_coe.mp hzb)
    have hmin : z ≤ x ⊓ y := le_inf hzx hzy
    simpa only [meet_embed_same, embed_le_embed_iff] using hmin

end WedgeNode
end GeneralTree
end Milliken
