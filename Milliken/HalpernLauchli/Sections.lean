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

/-- Adjoin a last coordinate set to a matrix: the cartesian product
\(M\times Y\). -/
def Matrix.snoc {d : ℕ} (M : Matrix ι d)
    (Y : Set (Node ι)) : Matrix ι (d + 1) where
  coord := Fin.lastCases Y M.coord

@[simp] theorem Matrix.snoc_coord_last {d : ℕ}
    (M : Matrix ι d) (Y : Set (Node ι)) :
    (M.snoc Y).coord (Fin.last d) = Y := by
  simp [Matrix.snoc]

@[simp] theorem Matrix.snoc_coord_castSucc {d : ℕ}
    (M : Matrix ι d) (Y : Set (Node ι)) (i : Fin d) :
    (M.snoc Y).coord i.castSucc = M.coord i := by
  simp [Matrix.snoc]

@[simp] theorem Matrix.mem_snoc_carrier_appendLast {d : ℕ}
    (M : Matrix ι d) (Y : Set (Node ι))
    (x : Fin d → Node ι) (y : Node ι) :
    appendLast x y ∈ (M.snoc Y).carrier ↔
      x ∈ M.carrier ∧ y ∈ Y := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [Matrix.snoc] using h i.castSucc
    · simpa [Matrix.snoc] using h (Fin.last d)
  · rintro ⟨hx, hy⟩ i
    exact Fin.lastCases
      (by simpa [Matrix.snoc] using hy)
      (fun j => by simpa [Matrix.snoc] using hx j)
      i

/-- Coordinatewise density above a base is preserved by adjoining a last
coordinate which is dense above its own base node. -/
theorem Matrix.snoc_denseAbove {d n : ℕ}
    {M : Matrix ι d} {Y : Set (Node ι)}
    {base : Fin d → Node ι} {t : Node ι}
    (hM : M.DenseAbove base n)
    (hY : HalpernLauchli.DenseAbove Y t n) :
    (M.snoc Y).DenseAbove (appendLast base t) n := by
  intro i u hu
  cases i using Fin.lastCases with
  | last =>
      have hut : u ∈ coneLevel t n := by
        simpa [appendLast] using hu
      simpa [Matrix.snoc] using hY hut
  | cast j =>
      have huj : u ∈ coneLevel (base j) n := by
        simpa [appendLast] using hu
      simpa [Matrix.snoc] using hM j huj

/-- A node exactly one level above a prefix is one of its literal children. -/
theorem exists_child_eq_of_prefix_length_succ
    {t u : Node ι} (htu : t.IsPrefix u)
    (hlen : u.length = t.length + 1) :
    ∃ i : ι, child t i = u := by
  rcases htu with ⟨r, rfl⟩
  have hrlen : r.length = 1 := by
    simp only [List.length_append] at hlen
    omega
  cases r with
  | nil =>
      omega
  | cons i r =>
      have hrzero : r.length = 0 := by
        simp only [List.length_cons] at hrlen
        omega
      have hrnil : r = [] := List.length_eq_zero.mp hrzero
      subst r
      exact ⟨i, by simp [child]⟩

/-- A set meeting every immediate successor cone dominates the next level
above `t`. -/
theorem denseAbove_succ_of_coversChildren
    (Y : Set (Node ι)) (t : Node ι)
    (hY : ∀ i : ι, ∃ y ∈ Y, (child t i).IsPrefix y) :
    DenseAbove Y t (t.length + 1) := by
  intro u hu
  rcases exists_child_eq_of_prefix_length_succ hu.1 hu.2 with
    ⟨i, hi⟩
  rcases hY i with ⟨y, hyY, hiy⟩
  refine ⟨y, hyY, ?_⟩
  rw [← hi]
  exact hiy

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

/-- If the same front matrix avoids every section indexed by `Y`,
then its product with `Y` avoids `P`. -/
theorem Matrix.snoc_carrier_subset_compl {d : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    (M : Matrix ι d) (Y : Set (Node ι))
    (havoid : ∀ y ∈ Y, M.carrier ⊆ (lastSection P y)ᶜ) :
    (M.snoc Y).carrier ⊆ Pᶜ := by
  intro z hz hP
  have hzFront : front z ∈ M.carrier := by
    intro i
    simpa [front, Matrix.snoc] using hz i.castSucc
  have hzLast : last z ∈ Y := by
    simpa [last, Matrix.snoc] using hz (Fin.last d)
  have hfrontP : front z ∈ lastSection P (last z) := by
    change appendLast (front z) (last z) ∈ P
    simpa [appendLast_front_last] using hP
  exact (havoid (last z) hzLast hzFront) hfrontP


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
