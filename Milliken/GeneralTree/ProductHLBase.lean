import Milliken.GeneralTree.ProductHL

/-!
# Verified base cases for heterogeneous product Halpern--Läuchli

The remaining general-product strong-tree Halpern--Läuchli theorem
is dimension- and colour-quantified. The empty product is trivial
for every finite number of colours; every positive-dimensional
product is trivial for a one-colour assignment because the initial
factors already have synchronized selected ambient levels.

These base cases make neither a homogeneous-tree assumption nor
a global branching-degree bound. The nontrivial induction for
arbitrary dimensions and at least two colours remains open.
-/

namespace Milliken
namespace GeneralTree

/-- The heterogeneous product HL statement is true in dimension zero
for an arbitrary positive finite number of colours. -/
theorem generalProductHL_dimZero
    (U : AmbientTree)
    (colors : ℕ) [NeZero colors]
    (P : Fin 0 → StrongSubtree U)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (colour : (Fin 0 → U) → Fin colors) :
    ∃ c : Fin colors,
      ∃ M : ℕ → ℕ,
        ∃ F : Fin 0 → StrongSubtree U,
          StrictMono M ∧
            (∀ i, (F i).Refines (P i) ∧ (F i).levels = M) ∧
            ∀ k : ℕ, ∀ x : Fin 0 → U,
              (∀ i, x i ∈ (F i).sourceLevel k) →
                colour x = c := by
  let x0 : Fin 0 → U := fun i => Fin.elim0 i
  refine ⟨colour x0, id, (fun i => Fin.elim0 i),
    strictMono_id, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro k x hx
    have heq : x = x0 := by
      funext i
      exact Fin.elim0 i
    rw [heq]

/-- One-colour heterogeneous HL holds for any finite dimension.
For a positive dimension the initial synchronized factors already
witness the conclusion; dimension zero uses the separate base case. -/
theorem generalProductHL_oneColour
    (U : AmbientTree)
    (d : ℕ)
    (P : Fin d → StrongSubtree U)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (colour : (Fin d → U) → Fin 1) :
    ∃ c : Fin 1,
      ∃ M : ℕ → ℕ,
        ∃ F : Fin d → StrongSubtree U,
          StrictMono M ∧
            (∀ i, (F i).Refines (P i) ∧ (F i).levels = M) ∧
            ∀ k : ℕ, ∀ x : Fin d → U,
              (∀ i, x i ∈ (F i).sourceLevel k) →
                colour x = c := by
  by_cases hd : d = 0
  · subst d
    exact generalProductHL_dimZero U 1 P L hP colour
  · let i0 : Fin d := ⟨0, Nat.pos_of_ne_zero hd⟩
    have hmono : StrictMono L := by
      rw [← hP i0]
      exact (P i0).levels_strictMono
    refine ⟨0, L, P, hmono, ?_, ?_⟩
    · intro i
      exact ⟨StrongSubtree.refines_refl (P i), hP i⟩
    · intro k x hx
      exact Subsingleton.elim (colour x) (0 : Fin 1)

end GeneralTree
end Milliken
