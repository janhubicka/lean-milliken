import Milliken.HalpernLauchli.Statement

/-!
# Density language for the Halpern--Läuchli proof

This file follows Section 3.1 of Todorčević's *Introduction to Ramsey Spaces*.
The proof in Section 3.2 is organized around dense sets and dense matrices,
so we expose those notions before formalizing the induction on the number of
factors.

For now the ambient tree is the homogeneous tree `ι^{<ω}`.  The definitions
are deliberately phrased in terms of prefix domination; the same API will be
lifted to Mathlib's `RootedTree` representation for the general Milliken
statement.
-/

namespace Milliken
namespace HalpernLauchli

universe u

variable {ι : Type u}

/-- The `n`th level of the homogeneous tree. -/
def treeLevel (n : ℕ) : Set (Node ι) :=
  {s | s.length = n}

/-- `X` dominates `Y` in the tree order. -/
def Dominates (X Y : Set (Node ι)) : Prop :=
  ∀ ⦃y⦄, y ∈ Y → ∃ x ∈ X, y.IsPrefix x

/-- A set of nodes is `k`-dense if it dominates the `k`th level. -/
def DenseAt (X : Set (Node ι)) (k : ℕ) : Prop :=
  Dominates X (treeLevel (ι := ι) k)

/-- Nodes on ambient level `k` extending a fixed node `s`. -/
def coneLevel (s : Node ι) (k : ℕ) : Set (Node ι) :=
  {t | s.IsPrefix t ∧ t.length = k}

/-- The localized `k`-`s`-density notion from Section 3.1. -/
def DenseAbove (X : Set (Node ι)) (s : Node ι) (k : ℕ) : Prop :=
  Dominates X (coneLevel s k)

/-- A level vector in a finite cartesian power of the tree. -/
def IsLevelVectorAt {d : ℕ} (k : ℕ) (x : Fin d → Node ι) : Prop :=
  ∀ i, (x i).length = k

/-- Density for an arbitrary subset of the cartesian product. -/
def ProductDenseAt {d : ℕ} (P : Set (Fin d → Node ι)) (k : ℕ) : Prop :=
  ∀ x, IsLevelVectorAt k x →
    ∃ y ∈ P, ∀ i, (x i).IsPrefix (y i)

/-- A matrix is a genuine cartesian product of coordinate sets. -/
structure Matrix (ι : Type u) (d : ℕ) where
  coord : Fin d → Set (Node ι)

namespace Matrix

variable {d : ℕ}

def carrier (M : Matrix ι d) : Set (Fin d → Node ι) :=
  {x | ∀ i, x i ∈ M.coord i}

def DenseAt (M : Matrix ι d) (k : ℕ) : Prop :=
  ∀ i, HalpernLauchli.DenseAt (M.coord i) k

def DenseAbove (M : Matrix ι d) (base : Fin d → Node ι) (k : ℕ) : Prop :=
  ∀ i, HalpernLauchli.DenseAbove (M.coord i) (base i) k

/-- The book's "somewhere dense matrix": all coordinates are dense above
one level-vector, at a common later level. -/
def SomewhereDense (M : Matrix ι d) : Prop :=
  ∃ base : Fin d → Node ι, ∃ k : ℕ,
    (∀ i, (base i).length < k) ∧ M.DenseAbove base k

/-- The full `k`th level product. -/
def fullLevel (k : ℕ) : Matrix ι d where
  coord := fun _ => treeLevel (ι := ι) k

theorem fullLevel_dense (k : ℕ) :
    (fullLevel (ι := ι) (d := d) k).DenseAt k := by
  intro i y hy
  exact ⟨y, hy, by simp⟩

/-- Coordinatewise density of a matrix is exactly enough to obtain density
of its cartesian carrier in the product. -/
theorem productDenseAt_carrier (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    ProductDenseAt M.carrier k := by
  intro x hx
  classical
  choose y hyCoord hxy using fun i =>
    hM i (show x i ∈ treeLevel (ι := ι) k from hx i)
  refine ⟨y, ?_, hxy⟩
  intro i
  exact hyCoord i

/-- Density is monotone under enlarging every coordinate set. -/
theorem denseAt_mono {M N : Matrix ι d} {k : ℕ}
    (hMN : ∀ i, M.coord i ⊆ N.coord i)
    (hM : M.DenseAt k) :
    N.DenseAt k := by
  intro i x hx
  rcases hM i (show x ∈ treeLevel (ι := ι) k from hx) with
    ⟨y, hy, hxy⟩
  exact ⟨y, hMN i hy, hxy⟩

/-- Carrier inclusion follows from coordinatewise inclusion. -/
theorem carrier_mono {M N : Matrix ι d}
    (hMN : ∀ i, M.coord i ⊆ N.coord i) :
    M.carrier ⊆ N.carrier := by
  intro x hx i
  exact hMN i (hx i)

/-- A 1-dense matrix is somewhere dense, witnessed above the vector of
roots and ambient level 1. -/
theorem denseAt_one_somewhereDense (M : Matrix ι d)
    (hM : M.DenseAt 1) :
    M.SomewhereDense := by
  let root : Fin d → Node ι := fun _ => []
  refine ⟨root, 1, ?_, ?_⟩
  · intro i
    simp [root]
  · intro i t ht
    exact hM i (show t ∈ treeLevel (ι := ι) 1 from ht.2)

end Matrix

/-- Restrict every coordinate of a matrix to nodes lying above a prescribed
base vector. -/
def Matrix.restrictAbove {d : ℕ} (M : Matrix ι d)
    (base : Fin d → Node ι) : Matrix ι d where
  coord := fun i => {y | y ∈ M.coord i ∧ (base i).IsPrefix y}

theorem Matrix.restrictAbove_carrier_subset {d : ℕ}
    (M : Matrix ι d) (base : Fin d → Node ι) :
    (M.restrictAbove base).carrier ⊆ M.carrier := by
  intro y hy i
  exact (hy i).1

theorem Matrix.restrictAbove_prefix {d : ℕ}
    (M : Matrix ι d) (base : Fin d → Node ι)
    {y : Fin d → Node ι}
    (hy : y ∈ (M.restrictAbove base).carrier) :
    ∀ i, (base i).IsPrefix (y i) := by
  intro i
  exact (hy i).2

/-- If `M` is dense at a level strictly above the base vector, restricting
to the corresponding cones gives a matrix dense above that base. -/
theorem Matrix.restrictAbove_denseAbove {d : ℕ}
    (M : Matrix ι d) (base : Fin d → Node ι) {n : ℕ}
    (hM : M.DenseAt n)
    (hbase : ∀ i, (base i).length < n) :
    (M.restrictAbove base).DenseAbove base n := by
  intro i t ht
  rcases hM i (show t ∈ treeLevel (ι := ι) n from ht.2) with
    ⟨y, hyM, hty⟩
  refine ⟨y, ?_, hty⟩
  exact ⟨hyM, ht.1.trans hty⟩

/-- A set contains a somewhere-dense matrix. -/
def ContainsSomewhereDense {d : ℕ}
    (P : Set (Fin d → Node ι)) : Prop :=
  ∃ M : Matrix ι d, M.SomewhereDense ∧ M.carrier ⊆ P

/-- Definition 3.4, in the form used for Theorem 3.6: every sufficiently
dense matrix meets `P` in a prescribed dense subset of the product. -/
def HighlyDense {d : ℕ} (P : Set (Fin d → Node ι)) : Prop :=
  ∀ k, ∃ n, ∀ M : Matrix ι d,
    M.DenseAt n → ProductDenseAt (P ∩ M.carrier) k

/-- Observation preceding Lemma 3.5 in Todorčević: if the complement of
`P` contains no somewhere-dense matrix, then `P` is highly dense.

The proof uses the book's witness `n = k+1`.  If a `(k+1)`-dense matrix
failed to meet `P` in a `k`-dense set, restrict it to the cones above the
missing level-`k` vector.  The restricted matrix is somewhere dense and is
entirely contained in the complement. -/
theorem highlyDense_of_compl_no_somewhereDense {d : ℕ}
    (P : Set (Fin d → Node ι))
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    HighlyDense P := by
  intro k
  refine ⟨k + 1, ?_⟩
  intro M hM
  intro x hx
  by_contra hxy
  push Not at hxy
  let N : Matrix ι d := M.restrictAbove x
  have hbase : ∀ i, (x i).length < k + 1 := by
    intro i
    rw [hx i]
    omega
  have hNdense : N.DenseAbove x (k + 1) := by
    dsimp [N]
    exact M.restrictAbove_denseAbove x hM hbase
  have hNsome : N.SomewhereDense :=
    ⟨x, k + 1, hbase, hNdense⟩
  have hNcompl : N.carrier ⊆ Pᶜ := by
    intro y hyN hyP
    have hyM : y ∈ M.carrier := by
      exact M.restrictAbove_carrier_subset x hyN
    have hprefix : ∀ i, (x i).IsPrefix (y i) :=
      M.restrictAbove_prefix x hyN
    rcases hxy y ⟨hyP, hyM⟩ with ⟨i, hi⟩
    exact hi (hprefix i)
  exact hno ⟨N, hNsome, hNcompl⟩


/-- The highly-dense-set formulation `HDHL_d` of Halpern--Läuchli
(Theorem 3.6). -/
def HDHL (ι : Type u) (d : ℕ) : Prop :=
  ∀ P : Set (Fin d → Node ι), HighlyDense P →
    ∀ k, 0 < k →
      ∃ M : Matrix ι d, M.DenseAt k ∧ M.carrier ⊆ P

/-- The somewhere-dense-matrix formulation `SDHL_d` (Theorem 3.1),
stated for finite colorings. -/
def SDHL (ι : Type u) (d : ℕ) : Prop :=
  ∀ (colors : ℕ) [NeZero colors]
      (c : (Fin d → Node ι) → Fin colors),
    ∃ color : Fin colors, ∃ M : Matrix ι d,
      M.SomewhereDense ∧
        ∀ x ∈ M.carrier, c x = color

/-- Binary somewhere-dense Halpern--Läuchli follows from the highly-dense
form.  This is the only color arity needed for the A.4 proof in Chapter 6.

If color 1 already contains a somewhere-dense matrix, we are done.  Otherwise
the complement of color 0 contains no such matrix, so color 0 is highly
dense.  `HDHL` then supplies a 1-dense matrix in color 0, which is somewhere
dense above the root vector. -/
theorem binarySDHL_of_hdhl {d : ℕ}
    (hHDHL : HDHL ι d)
    (c : (Fin d → Node ι) → Fin 2) :
    ∃ color : Fin 2, ∃ M : Matrix ι d,
      M.SomewhereDense ∧
        ∀ x ∈ M.carrier, c x = color := by
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  by_cases h1 : ContainsSomewhereDense K0ᶜ
  · rcases h1 with ⟨M, hM, hsub⟩
    refine ⟨1, M, hM, ?_⟩
    intro x hx
    have hxC : x ∈ K0ᶜ := hsub hx
    have hne : c x ≠ (0 : Fin 2) := by
      intro hzero
      exact hxC hzero
    apply Fin.eq_of_val_eq
    omega
  · have hK0 : HighlyDense K0 :=
      highlyDense_of_compl_no_somewhereDense K0 h1
    rcases hHDHL K0 hK0 1 (by omega) with ⟨M, hM, hsub⟩
    refine ⟨0, M, Matrix.denseAt_one_somewhereDense M hM, ?_⟩
    intro x hx
    exact hsub hx

end HalpernLauchli
end Milliken
