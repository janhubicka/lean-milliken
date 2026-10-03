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

end Matrix

/-- Definition 3.4, in the form used for Theorem 3.6: every sufficiently
dense matrix meets `P` in a prescribed dense subset of the product. -/
def HighlyDense {d : ℕ} (P : Set (Fin d → Node ι)) : Prop :=
  ∀ k, ∃ n, ∀ M : Matrix ι d,
    M.DenseAt n → ProductDenseAt (P ∩ M.carrier) k

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

end HalpernLauchli
end Milliken
