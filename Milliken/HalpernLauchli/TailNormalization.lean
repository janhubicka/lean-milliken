import Milliken.HalpernLauchli.Sections
import Milliken.HalpernLauchli.Asymmetric

/-!
# Tail normalization for the Section 3.2 proof

The stabilization property (*) controls a section `P_y` only on front
level-vectors whose level lies strictly above `y`.  In the printed proof of
Lemma 3.15, avoiding matrices are subsequently treated as though their
supporting level were automatically above `y`.  This is harmless after the
following normalization, but it is useful to make the step explicit in Lean.

We enlarge `P` by declaring every tuple `x⌢y` to belong to `P` whenever
all front coordinates of `x` lie no higher than `y`.  Thus:

* on the tail where (*) is used, the normalized set agrees with `P`;
* its complement is a subset of `Pᶜ`, so the hypothesis that `Pᶜ`
  contains no somewhere-dense matrix is preserved;
* any nonempty level matrix avoiding a normalized section must live
  strictly above the last-coordinate node.

This is the normalization implicitly needed for equation (3) on page 56.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Enlarge `P` on tuples whose front coordinates do not lie above the
last coordinate. -/
def tailNormalize {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    Set (Fin (d + 1) → Node ι) :=
  {z | z ∈ P ∨ ∀ i : Fin d, (front z i).length ≤ (last z).length}

@[simp] theorem mem_tailNormalize_appendLast {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (x : Fin d → Node ι) (y : Node ι) :
    appendLast x y ∈ tailNormalize P ↔
      appendLast x y ∈ P ∨
        ∀ i : Fin d, (x i).length ≤ y.length := by
  simp [tailNormalize, front_appendLast, last_appendLast]

/-- On a front level strictly above `y`, normalization does not change the
section.  Positivity of the front dimension supplies a coordinate witnessing
that the "low" disjunct is false. -/
theorem mem_lastSection_tailNormalize_of_above
    {d l : ℕ} (hd : 0 < d)
    (P : Set (Fin (d + 1) → Node ι))
    (y : Node ι) (x : Fin d → Node ι)
    (hx : IsLevelVectorAt l x)
    (hyl : y.length < l) :
    x ∈ lastSection (tailNormalize P) y ↔
      x ∈ lastSection P y := by
  change appendLast x y ∈ tailNormalize P ↔
    appendLast x y ∈ P
  rw [mem_tailNormalize_appendLast]
  constructor
  · intro h
    rcases h with hP | hlow
    · exact hP
    · let i0 : Fin d := ⟨0, hd⟩
      have := hlow i0
      rw [hx i0] at this
      omega
  · exact Or.inl

/-- Every front level at or below `y` belongs to the normalized section. -/
theorem mem_lastSection_tailNormalize_of_le
    {d l : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (y : Node ι) (x : Fin d → Node ι)
    (hx : IsLevelVectorAt l x)
    (hly : l ≤ y.length) :
    x ∈ lastSection (tailNormalize P) y := by
  change appendLast x y ∈ tailNormalize P
  rw [mem_tailNormalize_appendLast]
  right
  intro i
  rw [hx i]
  exact hly

/-- Tail normalization preserves the stabilization property (*). -/
theorem stabilized_tailNormalize
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P) :
    Stabilized (tailNormalize P) := by
  intro y l x hx hyl
  have hhigh :
      x ∈ lastSection (tailNormalize P) y ↔
        x ∈ lastSection P y :=
    mem_lastSection_tailNormalize_of_above hd P y x hx hyl
  let q := y.length + 1
  have hql : q ≤ l := by
    dsimp [q]
    omega
  have hxq :
      IsLevelVectorAt q (truncateVector q x) :=
    truncateVector_length hx hql
  have hyq : y.length < q := by
    dsimp [q]
    omega
  have htrunc :
      truncateVector q x ∈ lastSection (tailNormalize P) y ↔
        truncateVector q x ∈ lastSection P y :=
    mem_lastSection_tailNormalize_of_above
      hd P y (truncateVector q x) hxq hyq
  exact hhigh.trans ((hstab y l x hx hyl).trans htrunc.symm)

/-- Normalization only enlarges `P`. -/
theorem subset_tailNormalize {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    P ⊆ tailNormalize P := by
  intro z hz
  exact Or.inl hz

/-- Consequently the normalized complement is contained in the original
complement. -/
theorem tailNormalize_compl_subset {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    (tailNormalize P)ᶜ ⊆ Pᶜ := by
  intro z hz hP
  exact hz (subset_tailNormalize P hP)

/-- The "no somewhere-dense matrix in the complement" hypothesis survives
tail normalization. -/
theorem no_somewhereDense_compl_tailNormalize {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    ¬ ContainsSomewhereDense (tailNormalize P)ᶜ := by
  rintro ⟨M, hM, hsub⟩
  exact hno ⟨M, hM, hsub.trans (tailNormalize_compl_subset P)⟩

end HalpernLauchli
end Milliken
