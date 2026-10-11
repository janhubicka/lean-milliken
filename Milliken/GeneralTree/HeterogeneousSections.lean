import Milliken.GeneralTree.HeterogeneousAsymmetric

/-!
# Product sections and matrix extension in heterogeneous HL induction

The source Todorčević proof of HDHL_(d+1) fixes the last tree
coordinate and colors the sections of the d-coordinate product.

These are the exact finite-index front/last operations for
arbitrary strong trees inside one locally finitely branching
ambient U, with no globally fixed branching alphabet.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Append the last coordinate to a finite heterogeneous tuple. -/
def heteroAppendLast (x : Fin d → U) (y : U) :
    Fin (d + 1) → U :=
  Fin.lastCases y x

@[simp] theorem heteroAppendLast_last
    (x : Fin d → U) (y : U) :
    heteroAppendLast x y (Fin.last d) = y := by
  simp [heteroAppendLast]

@[simp] theorem heteroAppendLast_castSucc
    (x : Fin d → U) (y : U) (i : Fin d) :
    heteroAppendLast x y i.castSucc = x i := by
  simp [heteroAppendLast]

/-- Restrict a d+1 tuple to its first d coordinates. -/
def heteroFront (z : Fin (d + 1) → U) :
    Fin d → U :=
  fun i => z i.castSucc

/-- Read the last coordinate of a d+1 tuple. -/
def heteroLast (z : Fin (d + 1) → U) : U :=
  z (Fin.last d)

@[simp] theorem heteroFront_appendLast
    (x : Fin d → U) (y : U) :
    heteroFront (heteroAppendLast x y) = x := by
  funext i
  simp [heteroFront]

@[simp] theorem heteroLast_appendLast
    (x : Fin d → U) (y : U) :
    heteroLast (heteroAppendLast x y) = y := by
  simp [heteroLast]

theorem heteroAppendLast_front_last
    (z : Fin (d + 1) → U) :
    heteroAppendLast (heteroFront z) (heteroLast z) = z := by
  funext i
  exact Fin.lastCases
    (by simp [heteroAppendLast, heteroLast])
    (fun j => by simp [heteroAppendLast, heteroFront])
    i

namespace HeterogeneousMatrix

/-- Append one coordinate set to a heterogeneous matrix. The new
coordinate is required to belong to the carrier of its actual
strong-tree factor. -/
def snoc
    (P : Fin (d + 1) → StrongSubtree U)
    (M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hY : Y ⊆ (P (Fin.last d)).carrier) :
    HeterogeneousMatrix P where
  coord := Fin.lastCases Y M.coord
  coord_sub := by
    intro i z hz
    cases i using Fin.lastCases with
    | last =>
        exact hY (by simpa using hz)
    | cast j =>
        exact M.coord_sub j (by simpa using hz)

/-- Product-carrier membership of the appended matrix is precisely
membership in the front matrix together with last-coordinate
membership in Y. -/
theorem mem_snoc_carrier_appendLast
    (P : Fin (d + 1) → StrongSubtree U)
    (M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hY : Y ⊆ (P (Fin.last d)).carrier)
    (x : Fin d → U) (y : U) :
    heteroAppendLast x y ∈ (snoc P M Y hY).carrier ↔
      x ∈ M.carrier ∧ y ∈ Y := by
  constructor
  · intro h
    constructor
    · intro i
      simpa [snoc] using h i.castSucc
    · simpa [snoc] using h (Fin.last d)
  · rintro ⟨hx, hy⟩ i
    exact Fin.lastCases
      (by simpa [snoc] using hy)
      (fun j => by simpa [snoc] using hx j)
      i

/-- Density at a selected source level is preserved by adjoining
a last coordinate dense on the same source level. -/
theorem snoc_denseAt
    (P : Fin (d + 1) → StrongSubtree U)
    (M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hY : Y ⊆ (P (Fin.last d)).carrier)
    (n : ℕ) (hM : M.DenseAt n)
    (hYdense : ∀ z ∈ (P (Fin.last d)).sourceLevel n,
      ∃ w, w ∈ Y ∧ z ≤ w) :
    (snoc P M Y hY).DenseAt n := by
  intro i z hz
  cases i using Fin.lastCases with
  | last =>
      simpa [snoc] using hYdense z hz
  | cast j =>
      simpa [snoc] using hM j z hz

end HeterogeneousMatrix

/-- Section of a d+1-product colour class at fixed last-coordinate
node y, exactly as in Todorčević's §3.2 proof. -/
def heterogeneousLastSection
    (Q : Set (Fin (d + 1) → U)) (y : U) :
    Set (Fin d → U) :=
  {x | heteroAppendLast x y ∈ Q}

@[simp] theorem heterogeneousLastSection_compl
    (Q : Set (Fin (d + 1) → U)) (y : U) :
    heterogeneousLastSection Qᶜ y =
      (heterogeneousLastSection Q y)ᶜ := by
  ext x
  rfl

/-- If the front matrix avoids every section indexed by Y, then
its product with Y avoids the original (d+1)-colour class. -/
theorem heterogeneousSnoc_carrier_subset_compl
    (P : Fin (d + 1) → StrongSubtree U)
    (M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hY : Y ⊆ (P (Fin.last d)).carrier)
    (Q : Set (Fin (d + 1) → U))
    (havoid : ∀ y ∈ Y,
      M.carrier ⊆ (heterogeneousLastSection Q y)ᶜ) :
    (M.snoc P Y hY).carrier ⊆ Qᶜ := by
  intro z hz hzQ
  have hfront : heteroFront z ∈ M.carrier := by
    intro i
    simpa [heteroFront, HeterogeneousMatrix.snoc]
      using hz i.castSucc
  have hlast : heteroLast z ∈ Y := by
    simpa [heteroLast, HeterogeneousMatrix.snoc]
      using hz (Fin.last d)
  have hsection :
      heteroFront z ∈
        heterogeneousLastSection Q (heteroLast z) := by
    change heteroAppendLast (heteroFront z) (heteroLast z) ∈ Q
    simpa only [heteroAppendLast_front_last] using hzQ
  exact (havoid (heteroLast z) hlast hfront) hsection

end GeneralTree
end Milliken
