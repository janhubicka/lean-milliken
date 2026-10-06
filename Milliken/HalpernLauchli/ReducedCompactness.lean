import Milliken.HalpernLauchli.ReducedInductionStep
import Milliken.HalpernLauchli.FiniteHLTransport

/-!
# Compactness for the reduced Halpern--Läuchli dichotomy

The induction proof in Section 3.2 first establishes only the reduced
dichotomy: if the complement contains no somewhere-dense matrix, then the
set contains a 1-dense matrix.  Remark 3.8 then changes the level structure
to recover the highly-dense formulation.

This file performs the compactness part of that reduction before any change
of levels.  The important output is finite: for a fixed alphabet and
dimension, finitely many finite monochromatic witnesses already cover all
binary colorings.  Hence there is one finite support bound beyond which the
level-restriction argument never has to look.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- The reduced form used in the Chapter 3 induction step. -/
def ReducedDichotomy (ι : Type u) (d : ℕ) : Prop :=
  ∀ P : Set (Fin d → Node ι),
    (¬ ContainsSomewhereDense Pᶜ) →
      ∃ M : Matrix ι d,
        M.DenseAt 1 ∧ M.carrier ⊆ P

/-- The product stabilization and Lemmas 3.15--3.16 establish the reduced
dichotomy in dimension `d+1` from HDHL in positive dimension `d`. -/
theorem reducedDichotomy_succ_of_hdhl
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d) :
    ReducedDichotomy ι (d + 1) := by
  intro P hno
  exact exists_one_dense_of_no_somewhereDense_succ
    hd hHDHL P hno

/-- Every binary coloring has a finite witness for the reduced dichotomy. -/
theorem exists_finiteHLWitness_of_reduced
    [Finite ι] [Nonempty ι]
    {d : ℕ}
    (hred : ReducedDichotomy ι d)
    (c : BinaryColoring ι d) :
    ∃ W : FiniteHLWitness ι d 1,
      c ∈ W.cylinder := by
  classical
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  by_cases hbad : ContainsSomewhereDense K0ᶜ
  · rcases hbad with
      ⟨M, ⟨base, q, hbase, hMdense⟩, hMsub⟩
    let N : Matrix ι d :=
      M.finiteDenseAboveCore base hMdense
    have hNsome : N.SomewhereDense := by
      refine ⟨base, q, hbase, ?_⟩
      dsimp [N]
      exact M.finiteDenseAboveCore_dense base hMdense
    let W : FiniteHLWitness ι d 1 := {
      M := N
      color := 1
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseAboveCore_coord_finite base hMdense
      shape := Or.inr ⟨rfl, hNsome⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier := by
      exact M.finiteDenseAboveCore_subset base hMdense hx
    have hx1 : x ∈ K0ᶜ := hMsub hxM
    apply Fin.eq_one_of_ne_zero
    intro hx0
    exact hx1 hx0
  · rcases hred K0 hbad with
      ⟨M, hMdense, hMsub⟩
    let N : Matrix ι d := M.finiteDenseCore hMdense
    let W : FiniteHLWitness ι d 1 := {
      M := N
      color := 0
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseCore_coord_finite hMdense
      shape := Or.inl ⟨rfl, by
        dsimp [N]
        exact M.finiteDenseCore_dense hMdense⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier :=
      M.finiteDenseCore_subset hMdense hx
    exact hMsub hxM

/-- The finite witness cylinders supplied by the reduced dichotomy cover the
whole binary-coloring space. -/
theorem reducedFiniteHLWitness_cover
    [Finite ι] [Nonempty ι]
    {d : ℕ}
    (hred : ReducedDichotomy ι d) :
    (Set.univ : Set (BinaryColoring ι d)) ⊆
      ⋃ W : FiniteHLWitness ι d 1, W.cylinder := by
  intro c hc
  rcases exists_finiteHLWitness_of_reduced hred c with
    ⟨W, hW⟩
  exact Set.mem_iUnion.2 ⟨W, hW⟩

/-- Compactness extracts finitely many reduced witnesses. -/
theorem exists_reducedFiniteHLWitness_subcover
    [Finite ι] [Nonempty ι]
    {d : ℕ}
    (hred : ReducedDichotomy ι d) :
    ∃ F : Finset (FiniteHLWitness ι d 1),
      (Set.univ : Set (BinaryColoring ι d)) ⊆
        ⋃ W ∈ F, W.cylinder := by
  classical
  exact isCompact_univ.elim_finite_subcover
    (fun W : FiniteHLWitness ι d 1 => W.cylinder)
    (fun W => W.cylinder_isOpen)
    (reducedFiniteHLWitness_cover hred)

end HalpernLauchli
end Milliken
