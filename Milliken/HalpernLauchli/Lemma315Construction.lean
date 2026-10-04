import Milliken.HalpernLauchli.Lemma315Normalized

/-!
# The finite recursive construction in Lemma 3.15

This file formalizes the "and so on" paragraph leading to equation (3).
After tail normalization, we recursively process a finite set of immediate
successor labels of a fixed node `t`.

The state remembers:
* a common-level matrix still dense at the original scale;
* a finite set of chosen last-coordinate nodes;
* avoidance of every corresponding section;
* that all chosen last-coordinate nodes lie below the matrix support;
* one chosen node above every processed immediate successor of `t`.

At a new branch label we choose a fresh avoiding witness from the minimal
cover at a scale above the current support and apply
`normalized_refinement_step`.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- State after processing the branch labels in `E`. -/
structure NormalizedAvoidState
    {d k n0 : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (x : LevelVector ι d k)
    (t : Node ι)
    (E : Finset ι) where
  M : Matrix ι d
  level : ℕ
  Y : Finset (Node ι)
  onLevel : M.OnLevel level
  dense : M.DenseAbove x.1 n0
  aboveBase :
    ∀ z ∈ M.carrier, ∀ i, (x.1 i).IsPrefix (z i)
  avoids :
    M.AvoidsSections (tailNormalize P) (Y : Set (Node ι))
  belowSupport :
    ∀ y ∈ Y, y.length < level
  covers :
    ∀ i ∈ E, ∃ y ∈ Y, (child t i).IsPrefix y
  baseBelowSupport : k < level

/-- Initial state before processing any successor: the full level
`|t|+1`, restricted to the cone above the fixed level-`k` vector. -/
noncomputable def initialNormalizedAvoidState
    [Nonempty ι] {d k : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (x : LevelVector ι d k)
    (t : Node ι)
    (hkt : k ≤ t.length) :
    NormalizedAvoidState P x t (∅ : Finset ι) := by
  classical
  let n0 := t.length + 1
  let F : Matrix ι d := Matrix.fullLevel n0
  let M : Matrix ι d := F.restrictAbove x.1
  have hbase : ∀ i, (x.1 i).length < n0 := by
    intro i
    rw [x.2 i]
    dsimp [n0]
    omega
  exact {
    M := M
    level := n0
    Y := ∅
    onLevel := by
      dsimp [M, F]
      exact Matrix.restrictAbove_onLevel
        (Matrix.fullLevel_onLevel (ι := ι) (d := d) n0)
    dense := by
      dsimp [M, F]
      exact Matrix.restrictAbove_denseAbove
        (Matrix.fullLevel (ι := ι) (d := d) n0)
        x.1
        (Matrix.fullLevel_dense (ι := ι) (d := d) n0)
        hbase
    aboveBase := by
      intro z hz i
      dsimp [M] at hz
      exact Matrix.restrictAbove_prefix F x.1 hz i
    avoids := by
      intro y hy
      simp at hy
    belowSupport := by
      intro y hy
      simp at hy
    covers := by
      intro i hi
      simp at hi
    baseBelowSupport := by
      dsimp [n0]
      omega
  }

/-- Process any prescribed finite set of immediate successor labels. -/
theorem exists_normalizedAvoidState
    [Finite ι] [Nonempty ι]
    {d k : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    {X : Set (Node ι)}
    (C : AvoidCover (tailNormalize P) k X)
    (hmin :
      ∀ C' : AvoidCover (tailNormalize P) k X,
        C.D.card ≤ C'.D.card)
    (x : LevelVector ι d k) (hxD : x ∈ C.D)
    (t : Node ι) (hrt : C.root.IsPrefix t)
    (hkt : k ≤ t.length)
    (E : Finset ι) :
    Nonempty (NormalizedAvoidState P x t E) := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      exact ⟨initialNormalizedAvoidState P x t hkt⟩
  | @insert i E hi ih =>
      rcases ih with ⟨S⟩
      let n := S.level + 1
      have hrootChild :
          C.root.IsPrefix (child t i) := by
        exact hrt.trans (List.prefix_append t [i])
      rcases exists_avoidWitness_above_of_minimal
          C hmin hxD hrootChild n with
        ⟨y, hchildy, hyC, hybad, hyavoid⟩
      have hkn : k < n := by
        dsimp [n]
        exact S.baseBelowSupport.trans (Nat.lt_succ_self _)
      have hstep := normalized_refinement_step
        hd hstab x S.M (S.Y : Set (Node ι))
        S.onLevel S.dense S.aboveBase S.avoids
        S.belowSupport (Nat.lt_succ_self S.level) hkn hyavoid
      rcases hstep with
        ⟨M', l', hlevel', hdense', habove',
          havoid', hbelow', hlvl'⟩
      let Y' : Finset (Node ι) := insert y S.Y
      refine ⟨{
        M := M'
        level := l'
        Y := Y'
        onLevel := hlevel'
        dense := hdense'
        aboveBase := habove'
        avoids := ?_
        belowSupport := ?_
        covers := ?_
        baseBelowSupport := S.baseBelowSupport.trans hlvl'
      }⟩
      · intro z hz
        have hz' :
            z ∈ Set.insert y (S.Y : Set (Node ι)) := by
          simpa [Y'] using hz
        exact havoid' z hz'
      · intro z hz
        have hz' :
            z ∈ Set.insert y (S.Y : Set (Node ι)) := by
          simpa [Y'] using hz
        exact hbelow' z hz'
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjE
        · exact ⟨y, by simp [Y'], hchildy⟩
        · rcases S.covers j hjE with ⟨z, hzY, hjz⟩
          exact ⟨z, by simp [Y', hzY], hjz⟩

end HalpernLauchli
end Milliken
