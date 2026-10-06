import Milliken.HalpernLauchli.Lemma315Proof

/-!
# The tower used in Lemma 3.16

Todorčević iterates Lemma 3.15 to obtain a strictly increasing sequence
`n₀<n₁<...` and decreasing somewhere-dense sets `X₀⊇X₁⊇...` satisfying
property (4).

Lemma 3.15 itself gives a suitable next density scale, but does not need to
state that this scale is larger than the current one.  This file makes the
harmless adjustment explicit: replace the returned scale `m` by
`max m (k+1)`.  Density at the larger input scale implies density at the
old one, so the section conclusion is preserved.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- If one input density scale works uniformly for all sections, then every
larger input density scale works as well. -/
theorem sectionsGoodAt_mono_input
    [Nonempty ι] {d k n m : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {Y : Set (Node ι)}
    (hnm : n ≤ m)
    (hgood : SectionsGoodAt P k n Y) :
    SectionsGoodAt P k m Y := by
  intro y hy M hM
  exact hgood y hy M (M.levelDenseAt_of_le hnm hM)

/-- Strict-growth form of Lemma 3.15. -/
theorem lemma315_tailNormalize_step
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (X : Set (Node ι))
    (hX : SomewhereConeDense X) :
    ∃ n : ℕ, ∃ Y : Set (Node ι),
      k < n ∧ Y ⊆ X ∧ SomewhereConeDense Y ∧
        SectionsGoodAt (tailNormalize P) k n Y := by
  rcases lemma315_tailNormalize hd hstab hno k X hX with
    ⟨m, Y, hYX, hYdense, hgood⟩
  let n := max m (k + 1)
  have hmn : m ≤ n := by
    dsimp [n]
    exact Nat.le_max_left _ _
  have hkn : k < n := by
    dsimp [n]
    exact lt_of_lt_of_le (Nat.lt_succ_self k) (Nat.le_max_right _ _)
  exact ⟨n, Y, hkn, hYX, hYdense,
    sectionsGoodAt_mono_input hmn hgood⟩

/-- One state of the Lemma 3.16 iteration. -/
structure Lemma315TowerState (ι : Type u) where
  n : ℕ
  X : Set (Node ι)
  dense : SomewhereConeDense X

/-- Chosen next state supplied by the strict-growth Lemma 3.15 step. -/
noncomputable def nextLemma315TowerState
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : Lemma315TowerState ι) :
    Lemma315TowerState ι := by
  classical
  let h := lemma315_tailNormalize_step
    hd hstab hno S.n S.X S.dense
  exact ⟨Classical.choose h,
    Classical.choose (Classical.choose_spec h),
    (Classical.choose_spec (Classical.choose_spec h)).2.2.1⟩

theorem nextLemma315TowerState_n_lt
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : Lemma315TowerState ι) :
    S.n < (nextLemma315TowerState hd hstab hno S).n := by
  classical
  let h := lemma315_tailNormalize_step
    hd hstab hno S.n S.X S.dense
  exact (Classical.choose_spec
    (Classical.choose_spec h)).1

theorem nextLemma315TowerState_subset
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : Lemma315TowerState ι) :
    (nextLemma315TowerState hd hstab hno S).X ⊆ S.X := by
  classical
  let h := lemma315_tailNormalize_step
    hd hstab hno S.n S.X S.dense
  exact (Classical.choose_spec
    (Classical.choose_spec h)).2.1

theorem nextLemma315TowerState_good
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : Lemma315TowerState ι) :
    SectionsGoodAt (tailNormalize P)
      S.n (nextLemma315TowerState hd hstab hno S).n
      (nextLemma315TowerState hd hstab hno S).X := by
  classical
  let h := lemma315_tailNormalize_step
    hd hstab hno S.n S.X S.dense
  exact (Classical.choose_spec
    (Classical.choose_spec h)).2.2.2

/-- The recursively chosen tower from Lemma 3.16, starting with the cone
above `t` and initial density parameter `k`. -/
noncomputable def lemma315Tower
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    ℕ → Lemma315TowerState ι
  | 0 => ⟨k, coneSet t, cone_somewhereDense t⟩
  | p + 1 =>
      nextLemma315TowerState hd hstab hno
        (lemma315Tower hd hstab hno k t p)

@[simp] theorem lemma315Tower_zero_n
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    (lemma315Tower hd hstab hno k t 0).n = k := rfl

@[simp] theorem lemma315Tower_zero_X
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    (lemma315Tower hd hstab hno k t 0).X = coneSet t := rfl

theorem lemma315Tower_n_lt_succ
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    (lemma315Tower hd hstab hno k t p).n <
      (lemma315Tower hd hstab hno k t (p + 1)).n := by
  exact nextLemma315TowerState_n_lt
    hd hstab hno (lemma315Tower hd hstab hno k t p)

theorem lemma315Tower_X_succ_subset
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    (lemma315Tower hd hstab hno k t (p + 1)).X ⊆
      (lemma315Tower hd hstab hno k t p).X := by
  exact nextLemma315TowerState_subset
    hd hstab hno (lemma315Tower hd hstab hno k t p)

theorem lemma315Tower_good
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    SectionsGoodAt (tailNormalize P)
      (lemma315Tower hd hstab hno k t p).n
      (lemma315Tower hd hstab hno k t (p + 1)).n
      (lemma315Tower hd hstab hno k t (p + 1)).X := by
  exact nextLemma315TowerState_good
    hd hstab hno (lemma315Tower hd hstab hno k t p)

end HalpernLauchli
end Milliken
