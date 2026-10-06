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


namespace Matrix

/-- A matrix avoids every section indexed by `Y`. -/
def AvoidsSections {d : ℕ}
    (M : Matrix ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (Y : Set (Node ι)) : Prop :=
  ∀ y ∈ Y, M.carrier ⊆ (lastSection P y)ᶜ

end Matrix

/-- One recursive step in the corrected equation-(3) construction.

The old matrix `A` is already dense at the original scale, lies above the
fixed base vector, and avoids all sections in `Y`.  Choose the next
normalized avoiding witness at a new scale `n` strictly above the support
of `A`, and refine that new witness over `A`.

The resulting matrix:
* keeps the original density;
* remains above the base vector;
* avoids all old sections and the new section;
* has a strictly later support, above every section parameter processed so
  far.

This is the explicit nested-matrix step hidden in the printed proof of (3).
-/
theorem normalized_refinement_step
    [Nonempty ι] {d k n0 n lA : ℕ}
    (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (x : LevelVector ι d k)
    (A : Matrix ι d)
    (Y : Set (Node ι))
    (hAlevel : A.OnLevel lA)
    (hAdense : A.DenseAbove x.1 n0)
    (hAprefix :
      ∀ z ∈ A.carrier, ∀ i, (x.1 i).IsPrefix (z i))
    (hAavoid :
      A.AvoidsSections (tailNormalize P) Y)
    (hYbelow : ∀ y ∈ Y, y.length < lA)
    (hlAn : lA < n)
    (hkn : k < n)
    {y : Node ι}
    (hnew :
      SectionAvoidAt (tailNormalize P) y x.1 n) :
    ∃ C : Matrix ι d, ∃ lC : ℕ,
      C.OnLevel lC ∧
      C.DenseAbove x.1 n0 ∧
      (∀ z ∈ C.carrier, ∀ i, (x.1 i).IsPrefix (z i)) ∧
      C.AvoidsSections (tailNormalize P) (Set.insert y Y) ∧
      (∀ z ∈ Set.insert y Y, z.length < lC) ∧
      lA < lC := by
  classical
  rcases sectionAvoidAt_tailNormalize_witness
      hd x hkn hnew with
    ⟨B, lB, hBlevel, hBdense, hBavoid, hBprefix, hyB⟩
  have hnB : n ≤ lB :=
    B.support_ge_of_onLevel_denseAbove
      hd x.2 hkn.le hBlevel hBdense
  have hAB : lA < lB := hlAn.trans_le hnB
  let C : Matrix ι d := A.refineOver B
  have hClevel : C.OnLevel lB := by
    dsimp [C]
    exact Matrix.refineOver_onLevel hBlevel
  have hCdense : C.DenseAbove x.1 n0 := by
    dsimp [C]
    exact Matrix.refineOver_denseAbove
      hAlevel hAdense hBdense hlAn.le
  have hCprefix :
      ∀ z ∈ C.carrier, ∀ i, (x.1 i).IsPrefix (z i) := by
    intro z hz i
    rcases Matrix.exists_predecessor_of_mem_refineOver hz with
      ⟨a, haA, haz⟩
    exact (hAprefix a haA i).trans (haz i)
  have hstabN : Stabilized (tailNormalize P) :=
    stabilized_tailNormalize hd hstab
  have hCold :
      C.AvoidsSections (tailNormalize P) Y := by
    intro z hzY
    dsimp [C]
    exact Matrix.refineOver_avoids_section
      hd hstabN hAlevel hBlevel
      (hYbelow z hzY) (hAavoid z hzY)
  have hCnew :
      C.carrier ⊆ (lastSection (tailNormalize P) y)ᶜ := by
    exact (Matrix.refineOver_carrier_subset_right A B).trans hBavoid
  have hCall :
      C.AvoidsSections (tailNormalize P) (Set.insert y Y) := by
    intro z hz
    rcases hz with rfl | hzY
    · exact hCnew
    · exact hCold z hzY
  have hbelow :
      ∀ z ∈ Set.insert y Y, z.length < lB := by
    intro z hz
    rcases hz with rfl | hzY
    · exact hyB
    · exact (hYbelow z hzY).trans hAB
  exact ⟨C, lB, hClevel, hCdense, hCprefix,
    hCall, hbelow, hAB⟩

end HalpernLauchli
end Milliken
