import Milliken.HalpernLauchli.Density

/-!
# Sections and stabilization for the HDHL induction

This file introduces the notation used in Todorčević, Section 3.2.  For
`P ⊆ ∏_{i≤d} T_i`, the section `P_y` fixes the last coordinate.  The
fusion preliminary to Lemma 3.15 arranges the stabilization property

  x ∈ P_y  ↔  (x ↾ (level(y)+1)) ∈ P_y

for level vectors `x` lying strictly above `y`.

We work with the homogeneous tree `List ι`; truncation is therefore literal
`List.take`.
-/

namespace Milliken
namespace HalpernLauchli

universe u

variable {ι : Type u}

/-- Append a last coordinate to a finite vector. -/
def appendLast {d : ℕ} (x : Fin d → Node ι) (y : Node ι) :
    Fin (d + 1) → Node ι :=
  Fin.lastCases y x

@[simp] theorem appendLast_last {d : ℕ}
    (x : Fin d → Node ι) (y : Node ι) :
    appendLast x y (Fin.last d) = y := by
  simp [appendLast]

@[simp] theorem appendLast_castSucc {d : ℕ}
    (x : Fin d → Node ι) (y : Node ι) (i : Fin d) :
    appendLast x y i.castSucc = x i := by
  simp [appendLast]

/-- Forget the last coordinate. -/
def front {d : ℕ} (z : Fin (d + 1) → Node ι) :
    Fin d → Node ι :=
  fun i => z i.castSucc

/-- Read the last coordinate. -/
def last {d : ℕ} (z : Fin (d + 1) → Node ι) : Node ι :=
  z (Fin.last d)

@[simp] theorem front_appendLast {d : ℕ}
    (x : Fin d → Node ι) (y : Node ι) :
    front (appendLast x y) = x := by
  funext i
  simp [front]

@[simp] theorem last_appendLast {d : ℕ}
    (x : Fin d → Node ι) (y : Node ι) :
    last (appendLast x y) = y := by
  simp [last]

theorem appendLast_front_last {d : ℕ}
    (z : Fin (d + 1) → Node ι) :
    appendLast (front z) (last z) = z := by
  funext i
  exact Fin.lastCases
    (by simp [appendLast, last])
    (fun j => by simp [appendLast, front])
    i

/-- The section `P_y` obtained by fixing the last coordinate. -/
def lastSection {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) (y : Node ι) :
    Set (Fin d → Node ι) :=
  {x | appendLast x y ∈ P}

@[simp] theorem mem_lastSection {d : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {y : Node ι} {x : Fin d → Node ι} :
    x ∈ lastSection P y ↔ appendLast x y ∈ P :=
  Iff.rfl

@[simp] theorem lastSection_compl {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) (y : Node ι) :
    lastSection Pᶜ y = (lastSection P y)ᶜ := by
  ext x
  rfl

/-- A vector with an appended last coordinate is a level vector precisely
when both pieces live on that same level. -/
theorem isLevelVectorAt_appendLast {d k : ℕ}
    {x : Fin d → Node ι} {y : Node ι} :
    IsLevelVectorAt k (appendLast x y) ↔
      IsLevelVectorAt k x ∧ y.length = k := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h i.castSucc
    · simpa using h (Fin.last d)
  · rintro ⟨hx, hy⟩ i
    exact Fin.lastCases
      (by simpa using hy)
      (fun j => by simpa using hx j)
      i

/-- Coordinatewise truncation of a vector of tree nodes. -/
def truncateVector {d : ℕ} (n : ℕ)
    (x : Fin d → Node ι) : Fin d → Node ι :=
  fun i => (x i).take n

theorem truncateVector_prefix {d n : ℕ}
    (x : Fin d → Node ι) :
    ∀ i, (truncateVector n x i).IsPrefix (x i) := by
  intro i
  exact List.take_prefix _ _

theorem truncateVector_length {d n l : ℕ}
    {x : Fin d → Node ι}
    (hx : IsLevelVectorAt l x)
    (hn : n ≤ l) :
    IsLevelVectorAt n (truncateVector n x) := by
  intro i
  dsimp [truncateVector]
  rw [List.length_take_of_le]
  simpa [hx i] using hn

/-- The stabilization property `(*)` on page 55 of the book. -/
def Stabilized {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) : Prop :=
  ∀ (y : Node ι) (l : ℕ) (x : Fin d → Node ι),
    IsLevelVectorAt l x →
    y.length < l →
      (x ∈ lastSection P y ↔
        truncateVector (y.length + 1) x ∈ lastSection P y)

/-- The basic open cone above a tree node. -/
def coneSet (t : Node ι) : Set (Node ι) :=
  {y | t.IsPrefix y}

/-- Restrict a set to a basic open cone. -/
def restrictCone (X : Set (Node ι)) (t : Node ι) : Set (Node ι) :=
  X ∩ coneSet t

/-- A subset is dense in the cone above `t` for the usual tree topology:
every extension of `t` has a further extension in the set. -/
def ConeDense (X : Set (Node ι)) (t : Node ι) : Prop :=
  ∀ ⦃u : Node ι⦄, t.IsPrefix u →
    ∃ y ∈ X, u.IsPrefix y

/-- The book's "somewhere τ₀-dense" property. -/
def SomewhereConeDense (X : Set (Node ι)) : Prop :=
  ∃ t, ConeDense X t

/-- The cone above `u` meets `X`. -/
def ConeMeets (X : Set (Node ι)) (u : Node ι) : Prop :=
  ∃ x ∈ X, u.IsPrefix x

/-- Topological density of `A` in the subspace `X`.  Every basic cone
which meets `X` also meets `A`. -/
def DenseIn (A X : Set (Node ι)) : Prop :=
  ∀ u, ConeMeets X u → ConeMeets A u

/-- `A` is somewhere dense relative to the subspace `X`: on one basic
cone it is dense in `X`. -/
def SomewhereDenseIn (A X : Set (Node ι)) : Prop :=
  ∃ t, ConeMeets X t ∧
    ∀ u, t.IsPrefix u → ConeMeets X u → ConeMeets A u

/-- Relative nowhere density. -/
def NowhereDenseIn (A X : Set (Node ι)) : Prop :=
  ¬ SomewhereDenseIn A X

theorem denseIn_mono_left {A B X : Set (Node ι)}
    (hAB : A ⊆ B) (hA : DenseIn A X) :
    DenseIn B X := by
  intro u hXu
  rcases hA u hXu with ⟨a, haA, hua⟩
  exact ⟨a, hAB haA, hua⟩

theorem somewhereConeDense_of_denseIn
    {A X : Set (Node ι)}
    (hX : SomewhereConeDense X)
    (hA : DenseIn A X) :
    SomewhereConeDense A := by
  rcases hX with ⟨t, hXt⟩
  refine ⟨t, ?_⟩
  intro u htu
  have hXu : ConeMeets X u := by
    rcases hXt htu with ⟨x, hxX, hux⟩
    exact ⟨x, hxX, hux⟩
  rcases hA u hXu with ⟨a, haA, hua⟩
  exact ⟨a, haA, hua⟩

theorem coneDense_mono {X Y : Set (Node ι)} {t : Node ι}
    (hXY : X ⊆ Y) (hX : ConeDense X t) :
    ConeDense Y t := by
  intro u htu
  rcases hX htu with ⟨y, hyX, huy⟩
  exact ⟨y, hXY hyX, huy⟩

/-- Restricting a cone-dense set to a deeper cone preserves density there. -/
theorem coneDense_restrictCone {X : Set (Node ι)} {t u : Node ι}
    (hX : ConeDense X t) (htu : t.IsPrefix u) :
    ConeDense (restrictCone X u) u := by
  intro v huv
  rcases hX (htu.trans huv) with ⟨y, hyX, hvy⟩
  refine ⟨y, ⟨hyX, ?_⟩, hvy⟩
  exact huv.trans hvy

theorem restrictCone_subset (X : Set (Node ι)) (t : Node ι) :
    restrictCone X t ⊆ X :=
  Set.inter_subset_left

/-- Failure of cone-density exposes a deeper basic cone missed by the set. -/
theorem not_coneDense_iff {X : Set (Node ι)} {t : Node ι} :
    ¬ ConeDense X t ↔
      ∃ u : Node ι, t.IsPrefix u ∧
        ∀ y ∈ X, ¬ u.IsPrefix y := by
  simp only [ConeDense]
  push Not
  rfl

theorem somewhereConeDense_mono {X Y : Set (Node ι)}
    (hXY : X ⊆ Y) (hX : SomewhereConeDense X) :
    SomewhereConeDense Y := by
  rcases hX with ⟨t, ht⟩
  exact ⟨t, coneDense_mono hXY ht⟩

/-- A cone itself is dense in that cone. -/
theorem cone_somewhereDense (t : Node ι) :
    SomewhereConeDense (coneSet t) := by
  refine ⟨t, ?_⟩
  intro u htu
  exact ⟨u, htu, by simp [coneSet]⟩

end HalpernLauchli
end Milliken
