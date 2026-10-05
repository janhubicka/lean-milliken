import Milliken.HalpernLauchli.Lemma316Tower

/-!
# A bounded-witness tower for Lemma 3.16

The proof of Lemma 3.16 eventually chooses a point `y ∈ X_l` whose level is
strictly below the selected density level `n_l`.  The printed proof treats
this as harmless bookkeeping: after Lemma 3.15 has produced the next set and
a working input scale, choose one point of that set and increase the scale
once more if necessary.

This file records that bookkeeping explicitly.  Every state of the new tower
contains a distinguished point of its somewhere cone-dense set below its
density parameter.  Increasing the input scale preserves `SectionsGoodAt`,
so the invariant costs nothing.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A somewhere cone-dense set is nonempty. -/
theorem exists_mem_of_somewhereConeDense
    {X : Set (Node ι)}
    (hX : SomewhereConeDense X) :
    ∃ y : Node ι, y ∈ X := by
  rcases hX with ⟨root, hroot⟩
  rcases hroot root (by simp) with ⟨y, hy, _⟩
  exact ⟨y, hy⟩

/-- A tower state together with a point already lying below its density
parameter. -/
structure Lemma316TowerState (ι : Type u) where
  n : ℕ
  X : Set (Node ι)
  dense : SomewhereConeDense X
  sample : Node ι
  sample_mem : sample ∈ X
  sample_below : sample.length < n

/-- The initial state.  We are free to start above the requested target
density `k`; a matrix dense at this larger level will still be `k`-dense.
Starting above `t` lets us use `t` itself as the first distinguished
point. -/
noncomputable def initialLemma316TowerState
    (k : ℕ) (t : Node ι) :
    Lemma316TowerState ι := {
  n := max k (t.length + 1)
  X := coneSet t
  dense := cone_somewhereDense t
  sample := t
  sample_mem := by
    simp [coneSet]
  sample_below := by
    have h :
        t.length + 1 ≤ max k (t.length + 1) :=
      Nat.le_max_right _ _
    omega
}

/-- The data supplied by one bounded-witness tower step. -/
structure Lemma316TowerStep {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (S : Lemma316TowerState ι) where
  next : Lemma316TowerState ι
  n_lt : S.n < next.n
  X_subset : next.X ⊆ S.X
  good : SectionsGoodAt P S.n next.n next.X

/-- Perform one Lemma 3.15 step, choose a point of the resulting
somewhere-dense set, and then enlarge the returned input scale beyond that
point. -/
noncomputable def nextLemma316TowerStep
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : Lemma316TowerState ι) :
    Lemma316TowerStep (tailNormalize P) S := by
  classical
  rcases lemma315_tailNormalize_step
      hd hstab hno S.n S.X S.dense with
    ⟨m, Y, hSm, hYS, hYdense, hgood⟩
  rcases exists_mem_of_somewhereConeDense hYdense with
    ⟨y, hyY⟩
  let n : ℕ := max m (y.length + 1)
  have hmn : m ≤ n := by
    dsimp [n]
    exact Nat.le_max_left _ _
  have hSn : S.n < n :=
    hSm.trans_le hmn
  have hyn : y.length < n := by
    have h :
        y.length + 1 ≤ n := by
      dsimp [n]
      exact Nat.le_max_right _ _
    omega
  let T : Lemma316TowerState ι := {
    n := n
    X := Y
    dense := hYdense
    sample := y
    sample_mem := hyY
    sample_below := hyn
  }
  refine {
    next := T
    n_lt := ?_
    X_subset := ?_
    good := ?_
  }
  · exact hSn
  · exact hYS
  · exact sectionsGoodAt_mono_input hmn hgood

/-- The recursively chosen bounded-witness tower. -/
noncomputable def lemma316Tower
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    ℕ → Lemma316TowerState ι
  | 0 => initialLemma316TowerState k t
  | p + 1 =>
      (nextLemma316TowerStep hd hstab hno
        (lemma316Tower hd hstab hno k t p)).next

@[simp] theorem lemma316Tower_zero_n
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    (lemma316Tower hd hstab hno k t 0).n =
      max k (t.length + 1) := rfl

@[simp] theorem lemma316Tower_zero_X
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    (lemma316Tower hd hstab hno k t 0).X =
      coneSet t := rfl

theorem lemma316Tower_target_le_zero
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    k ≤ (lemma316Tower hd hstab hno k t 0).n := by
  rw [lemma316Tower_zero_n]
  exact Nat.le_max_left _ _

theorem lemma316Tower_n_lt_succ
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    (lemma316Tower hd hstab hno k t p).n <
      (lemma316Tower hd hstab hno k t (p + 1)).n := by
  change
    (lemma316Tower hd hstab hno k t p).n <
      (nextLemma316TowerStep hd hstab hno
        (lemma316Tower hd hstab hno k t p)).next.n
  exact
    (nextLemma316TowerStep hd hstab hno
      (lemma316Tower hd hstab hno k t p)).n_lt

theorem lemma316Tower_X_succ_subset
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    (lemma316Tower hd hstab hno k t (p + 1)).X ⊆
      (lemma316Tower hd hstab hno k t p).X := by
  change
    (nextLemma316TowerStep hd hstab hno
      (lemma316Tower hd hstab hno k t p)).next.X ⊆
      (lemma316Tower hd hstab hno k t p).X
  exact
    (nextLemma316TowerStep hd hstab hno
      (lemma316Tower hd hstab hno k t p)).X_subset

theorem lemma316Tower_good
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    SectionsGoodAt (tailNormalize P)
      (lemma316Tower hd hstab hno k t p).n
      (lemma316Tower hd hstab hno k t (p + 1)).n
      (lemma316Tower hd hstab hno k t (p + 1)).X := by
  change
    SectionsGoodAt (tailNormalize P)
      (lemma316Tower hd hstab hno k t p).n
      (nextLemma316TowerStep hd hstab hno
        (lemma316Tower hd hstab hno k t p)).next.n
      (nextLemma316TowerStep hd hstab hno
        (lemma316Tower hd hstab hno k t p)).next.X
  exact
    (nextLemma316TowerStep hd hstab hno
      (lemma316Tower hd hstab hno k t p)).good

/-- Every chosen tower point belongs to its current set and lies below the
current density parameter. -/
theorem lemma316Tower_sample_spec
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) (p : ℕ) :
    (lemma316Tower hd hstab hno k t p).sample ∈
        (lemma316Tower hd hstab hno k t p).X ∧
      (lemma316Tower hd hstab hno k t p).sample.length <
        (lemma316Tower hd hstab hno k t p).n :=
  ⟨(lemma316Tower hd hstab hno k t p).sample_mem,
    (lemma316Tower hd hstab hno k t p).sample_below⟩

end HalpernLauchli
end Milliken
