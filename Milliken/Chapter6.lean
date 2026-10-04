import Milliken.GraftRamsey
import Milliken.HalpernLauchli.Statement
import Mathlib.Data.Set.Finite.List

/-!
# Chapter 6: Halpern--Läuchli on the boundary of a finite strong stem

This file begins the direct formalization of Todorčević, Lemma 6.1.
The first step is purely an indexing change: the strong-subtree
Halpern--Läuchli theorem is stated for a finite product indexed by `Fin d`,
whereas the one-step extension of an `n`-level strong tree has one
coordinate for each source node on level `n`.

Since that level is finite, the two forms are equivalent.  We expose the
boundary-indexed form so the rest of the Chapter 6 proof can follow the book
without carrying an arbitrary enumeration through every statement.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

/-- A level of the homogeneous finitely-branching tree is finite. -/
theorem finite_levelNode [Finite ι] (n : ℕ) :
    Finite (LevelNode ι n) :=
  (List.finite_length_eq ι n).to_subtype

/-- Halpern--Läuchli indexed directly by the boundary nodes of a finite
strong stem. -/
def BoundaryHL (ι : Type u) [Finite ι] [Nonempty ι] : Prop :=
  ∀ (n colors : ℕ) [NeZero colors]
      (c : (LevelNode ι n → Node ι) → Fin colors),
    ∃ color : Fin colors,
      ∃ F : LevelNode ι n → StrongEmbedding ι,
        BoundaryGraft.HasCommonLevels F ∧
          ∀ (m : ℕ) (x : LevelNode ι n → Node ι),
            (∀ q, (x q).length = m) →
              c (fun q => (F q).toFun (x q)) = color

/-- The standard `Fin d` formulation of strong-subtree Halpern--Läuchli
implies the boundary-indexed form needed in Lemma 6.1. -/
theorem boundaryHL_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι) :
    BoundaryHL ι := by
  intro n colors hcolors c
  letI : Finite (LevelNode ι n) := finite_levelNode n
  letI : Fintype (LevelNode ι n) := Fintype.ofFinite _
  let d := Fintype.card (LevelNode ι n)
  let e : Fin d ≃ LevelNode ι n :=
    (Fintype.equivFin (LevelNode ι n)).symm
  let c' : (Fin d → Node ι) → Fin colors :=
    fun x => c (fun q => x (e.symm q))
  rcases hHL d colors c' with
    ⟨color, levels, G, hGlevels, hhom⟩
  let F : LevelNode ι n → StrongEmbedding ι :=
    fun q => G (e.symm q)
  refine ⟨color, F, ?_, ?_⟩
  · refine ⟨levels, hGlevels.1, ?_⟩
    intro q s
    exact hGlevels.2 (e.symm q) s
  · intro m x hx
    have hh :=
      hhom m (fun i => x (e i)) (by
        intro i
        exact hx (e i))
    change c (fun q => (F q).toFun (x q)) = color
    simpa [c', F] using hh

end Chapter6
end Milliken
