import Milliken.HalpernLauchli.Lemma315Construction

/-!
# Lemma 3.15 after explicit tail normalization

This file closes the contradiction argument on page 56.  The only change
from the printed proof is that the harmless tail normalization and the
nested matrix refinements are explicit.

The conclusion is stated for the normalized set.  This is exactly what is
needed in Lemma 3.16: its eventual matrix is required to have support above
the chosen last-coordinate node, and on that tail the normalized and
original sections agree.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Corrected/formalized form of Todorčević's Lemma 3.15.

Under the induction-step standing hypotheses, every somewhere cone-dense
set of last coordinates contains a somewhere cone-dense subset on which one
density scale works uniformly for all sections of the tail-normalized set. -/
theorem lemma315_tailNormalize
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (X : Set (Node ι))
    (hX : SomewhereConeDense X) :
    ∃ n : ℕ, ∃ Y : Set (Node ι),
      Y ⊆ X ∧ SomewhereConeDense Y ∧
        SectionsGoodAt (tailNormalize P) k n Y := by
  classical
  by_contra hfail
  have hnoN :
      ¬ ContainsSomewhereDense (tailNormalize P)ᶜ :=
    no_somewhereDense_compl_tailNormalize P hno
  rcases exists_minimalAvoidCover
      (tailNormalize P) hX with
    ⟨C, hmin⟩
  rcases minimalAvoidCover_D_nonempty
      (P := tailNormalize P) hfail C with
    ⟨x, hxD⟩
  let l : ℕ := max k C.root.length
  let t : Node ι := extendToLevel C.root l
  have hrootL : C.root.length ≤ l := by
    dsimp [l]
    exact Nat.le_max_right _ _
  have hrt : C.root.IsPrefix t := by
    dsimp [t]
    exact prefix_extendToLevel _ _
  have htlen : t.length = l := by
    dsimp [t]
    exact length_extendToLevel hrootL
  have hkt : k ≤ t.length := by
    rw [htlen]
    dsimp [l]
    exact Nat.le_max_left _ _
  letI : Fintype ι := Fintype.ofFinite ι
  rcases exists_normalizedAvoidState
      hd hstab C hmin x hxD t hrt hkt Finset.univ with
    ⟨S⟩
  have hYdense :
      DenseAbove (S.Y : Set (Node ι)) t (t.length + 1) := by
    apply denseAbove_succ_of_coversChildren
    intro i
    rcases S.covers i (Finset.mem_univ i) with
      ⟨y, hyY, hiy⟩
    exact ⟨y, hyY, hiy⟩
  let M : Matrix ι (d + 1) :=
    S.M.snoc (S.Y : Set (Node ι))
  have hMdense :
      M.DenseAbove (appendLast x.1 t) (t.length + 1) := by
    dsimp [M]
    exact Matrix.snoc_denseAbove S.dense hYdense
  have hbase :
      ∀ i : Fin (d + 1),
        (appendLast x.1 t i).length < t.length + 1 := by
    intro i
    exact Fin.lastCases
      (by simp [appendLast])
      (fun j => by
        simp [appendLast, x.2 j]
        exact lt_of_le_of_lt hkt (Nat.lt_succ_self _))
      i
  have hMsome : M.SomewhereDense :=
    ⟨appendLast x.1 t, t.length + 1, hbase, hMdense⟩
  have hMsub :
      M.carrier ⊆ (tailNormalize P)ᶜ := by
    dsimp [M]
    exact Matrix.snoc_carrier_subset_compl
      S.M (S.Y : Set (Node ι)) S.avoids
  exact hnoN ⟨M, hMsome, hMsub⟩

end HalpernLauchli
end Milliken
