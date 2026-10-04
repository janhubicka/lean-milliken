import Milliken.HalpernLauchli.Lemma315
import Milliken.HalpernLauchli.TailNormalization
import Milliken.HalpernLauchli.MatrixRefinement

/-!
# Normalized avoiding witnesses for Lemma 3.15

After tail normalization, every genuine avoiding level matrix must live
strictly above the last-coordinate node.  We also trim the matrix to the cone
above the fixed level vector.  This gives the exact witness shape needed for
the recursive construction behind equation (3).
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A normalized section-avoidance witness can be chosen so that every point
of the matrix lies coordinatewise above the base vector, and the common
supporting level lies strictly above the section parameter. -/
theorem sectionAvoidAt_tailNormalize_witness
    [Nonempty ι] {d k n : ℕ}
    (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    {y : Node ι}
    (x : LevelVector ι d k)
    (hkn : k < n)
    (havoid :
      SectionAvoidAt (tailNormalize P) y x.1 n) :
    ∃ M : Matrix ι d, ∃ l : ℕ,
      M.OnLevel l ∧
      M.DenseAbove x.1 n ∧
      M.carrier ⊆ (lastSection (tailNormalize P) y)ᶜ ∧
      (∀ z ∈ M.carrier, ∀ i, (x.1 i).IsPrefix (z i)) ∧
      y.length < l := by
  classical
  rcases havoid with ⟨A, l, hAlevel, hAdense, hAavoid⟩
  let M : Matrix ι d := A.restrictAbove x.1
  have hMlevel : M.OnLevel l := by
    dsimp [M]
    exact A.restrictAbove_onLevel hAlevel
  have hMdense : M.DenseAbove x.1 n := by
    dsimp [M]
    exact A.restrictAbove_denseAbove_self hAdense
  have hMavoid :
      M.carrier ⊆ (lastSection (tailNormalize P) y)ᶜ :=
    (A.restrictAbove_carrier_subset x.1).trans hAavoid
  have hMprefix :
      ∀ z ∈ M.carrier, ∀ i, (x.1 i).IsPrefix (z i) := by
    intro z hz i
    dsimp [M] at hz
    exact A.restrictAbove_prefix x.1 hz i
  have hsupport : y.length < l := by
    by_contra hnot
    have hly : l ≤ y.length := le_of_not_gt hnot
    let u : Fin d → Node ι :=
      fun i => extendToLevel (x.1 i) n
    have hulen : IsLevelVectorAt n u := by
      intro i
      dsimp [u]
      apply length_extendToLevel
      rw [x.2 i]
      omega
    have hxprefix : ∀ i, (x.1 i).IsPrefix (u i) := by
      intro i
      dsimp [u]
      exact prefix_extendToLevel _ _
    choose z hzM huz using fun i =>
      hMdense i
        (show u i ∈ coneLevel (x.1 i) n from
          ⟨hxprefix i, hulen i⟩)
    have hzCarrier : z ∈ M.carrier := by
      intro i
      exact hzM i
    have hzLevel : IsLevelVectorAt l z := by
      intro i
      exact hMlevel i (z i) (hzM i)
    have hzNorm :
        z ∈ lastSection (tailNormalize P) y :=
      mem_lastSection_tailNormalize_of_le P y z hzLevel hly
    exact hMavoid hzCarrier hzNorm
  exact ⟨M, l, hMlevel, hMdense, hMavoid, hMprefix, hsupport⟩

/-- In particular, every normalized avoiding witness has some supporting
level strictly above the section parameter. -/
theorem sectionAvoidAt_tailNormalize_support_gt
    [Nonempty ι] {d k n : ℕ}
    (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    {y : Node ι}
    (x : LevelVector ι d k)
    (hkn : k < n)
    (havoid :
      SectionAvoidAt (tailNormalize P) y x.1 n) :
    ∃ l : ℕ, y.length < l := by
  rcases sectionAvoidAt_tailNormalize_witness
      hd x hkn havoid with
    ⟨M, l, hlevel, hdense, hsub, hprefix, hyl⟩
  exact ⟨l, hyl⟩

end HalpernLauchli
end Milliken
