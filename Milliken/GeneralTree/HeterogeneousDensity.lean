import Milliken.GeneralTree.ProductHL
import Milliken.GeneralTree.LongCones

/-!
# Todorčević's HDHL density calculus for genuinely heterogeneous trees

The original Chapter 3 `HDHL` proof uses homogeneous finite alphabets.
Here the proof is formulated directly for node-dependently branching ambient
rooted trees; the completed arbitrary-ambient theorem is exported in
`HeterogeneousUniversalMilliken`.

We define the corresponding finite-dimensional matrix and density
objects for arbitrary strong subtrees `P : Fin d → StrongSubtree U`
of one locally finitely branching pruned ambient tree. There is
no global branching bound. The underlying selected source levels
of individual factors need not share a common root or tree shape.

This module proves finiteness/nonemptiness of every finite level
product and elementary density transport, which are used by the
Chapter 3 induction. It defines the heterogeneous HDHL property; the proved universal theorem
inhabiting it is exported separately in `HeterogeneousUniversalMilliken`.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The product of the n-th selected source levels of arbitrary
coordinate strong trees, packaged with its source-level invariant. -/
def HeterogeneousLevelTuple (P : Fin d → StrongSubtree U) (n : ℕ) :=
  {x : Fin d → U // ∀ i, x i ∈ (P i).sourceLevel n}

/-- Local finiteness suffices to make every fixed source-level product
finite, even if branching degrees across the ambient tree are unbounded. -/
instance heterogeneousLevelTuple_finite
    (P : Fin d → StrongSubtree U) (n : ℕ) :
    Finite (HeterogeneousLevelTuple P n) := by
  classical
  letI : ∀ i : Fin d,
      Finite {z : U // z ∈ (P i).sourceLevel n} :=
    fun i => ((P i).sourceLevel_finite n).to_subtype
  let encode :
      HeterogeneousLevelTuple P n →
        (∀ i : Fin d, {z : U // z ∈ (P i).sourceLevel n}) :=
    fun x i => ⟨x.1 i, x.2 i⟩
  have hinj : Function.Injective encode := by
    intro x y hxy
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hxy i)
  exact Finite.of_injective encode hinj

/-- Every selected level product is nonempty. The dimension-zero
case is allowed and consists of the unique empty coordinate tuple. -/
instance heterogeneousLevelTuple_nonempty
    (P : Fin d → StrongSubtree U) (n : ℕ) :
    Nonempty (HeterogeneousLevelTuple P n) := by
  classical
  let x : Fin d → U :=
    fun i => Classical.choose ((P i).sourceLevel_nonempty n)
  exact ⟨⟨x, fun i =>
    Classical.choose_spec ((P i).sourceLevel_nonempty n)⟩⟩

/-- A coordinatewise matrix inside a possibly heterogeneous product.
Each coordinate is a set of retained nodes of its own strong tree. -/
structure HeterogeneousMatrix (P : Fin d → StrongSubtree U) where
  coord : Fin d → Set U
  coord_sub : ∀ i, coord i ⊆ (P i).carrier

namespace HeterogeneousMatrix

variable {P : Fin d → StrongSubtree U}

/-- Cartesian carrier of a heterogeneous matrix. -/
def carrier (M : HeterogeneousMatrix P) : Set (Fin d → U) :=
  {x | ∀ i, x i ∈ M.coord i}

/-- Global density at selected source height n: every coordinate
node at that level has an extension in the matrix's coordinate. -/
def DenseAt (M : HeterogeneousMatrix P) (n : ℕ) : Prop :=
  ∀ i : Fin d, ∀ x ∈ (P i).sourceLevel n,
    ∃ y, y ∈ M.coord i ∧ x ≤ y

/-- All coordinate sets lie on the indicated selected source level. -/
def OnLevel (M : HeterogeneousMatrix P) (n : ℕ) : Prop :=
  ∀ i : Fin d, ∀ x ∈ M.coord i,
    x ∈ (P i).sourceLevel n

/-- All nodes on a common selected source level form a matrix.
No assumption that the coordinates are isomorphic is necessary. -/
def fullLevel (P : Fin d → StrongSubtree U) (n : ℕ) :
    HeterogeneousMatrix P where
  coord := fun i => (P i).sourceLevel n
  coord_sub := fun _ x hx => hx.1

theorem fullLevel_denseAt (P : Fin d → StrongSubtree U) (n : ℕ) :
    (fullLevel P n).DenseAt n := by
  intro i x hx
  exact ⟨x, hx, le_rfl⟩

theorem fullLevel_onLevel (P : Fin d → StrongSubtree U) (n : ℕ) :
    (fullLevel P n).OnLevel n := by
  intro i x hx
  exact hx

/-- Dense at a later selected source level implies dense at any
earlier selected source level, using genuine strong-tree descendants. -/
theorem denseAt_of_le
    (M : HeterogeneousMatrix P) {m n : ℕ}
    (hmn : m ≤ n) (hM : M.DenseAt n) :
    M.DenseAt m := by
  intro i x hx
  obtain ⟨z, hz, hxz⟩ :=
    (P i).exists_sourceLevel_descendant hmn hx
  obtain ⟨y, hy, hzy⟩ := hM i z hz
  exact ⟨y, hy, hxz.trans hzy⟩

end HeterogeneousMatrix

/-- Coordinatewise product density above all level-n tuples. -/
def HeterogeneousProductDenseAt
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U)) (n : ℕ) : Prop :=
  ∀ x : HeterogeneousLevelTuple P n,
    ∃ y : Fin d → U, y ∈ Q ∧ ∀ i, x.1 i ≤ y i

/-- The source-faithful highly-dense-set antecedent from §3.2,
generalized to finite products of arbitrary locally finite strong trees. -/
def HeterogeneousHighlyDense
    (P : Fin d → StrongSubtree U)
    (Q : Set (Fin d → U)) : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, ∀ M : HeterogeneousMatrix P,
    M.DenseAt n →
      HeterogeneousProductDenseAt P (Q ∩ M.carrier) k

/-- The exact heterogeneous highly-dense Halpern--Läuchli
statement, analogous to the checked homogeneous `HDHL`.
This is a target *definition*, not an axiom. Its property is proved
universally in `HeterogeneousUniversalMilliken`. -/
def HasHeterogeneousHDHL
    (P : Fin d → StrongSubtree U) : Prop :=
  ∀ Q : Set (Fin d → U),
    HeterogeneousHighlyDense P Q →
    ∀ k : ℕ, 0 < k →
      ∃ M : HeterogeneousMatrix P,
        M.DenseAt k ∧ M.carrier ⊆ Q


/-- The highly-dense-set hypothesis is non-vacuous: the empty
colour class never satisfies it. For every k there is a nonempty
source-level tuple, while the full-level matrix at the proposed
test scale is itself dense. This is a useful adversarial regression
against accidentally weakening the density predicate. -/
theorem not_heterogeneousHighlyDense_empty
    (P : Fin d → StrongSubtree U) :
    ¬ HeterogeneousHighlyDense P (∅ : Set (Fin d → U)) := by
  classical
  intro h
  obtain ⟨n, hn⟩ := h 0
  have hDense :
      (HeterogeneousMatrix.fullLevel P n).DenseAt n :=
    HeterogeneousMatrix.fullLevel_denseAt P n
  have hProduct :
      HeterogeneousProductDenseAt P
        ((∅ : Set (Fin d → U)) ∩
          (HeterogeneousMatrix.fullLevel P n).carrier) 0 :=
    hn (HeterogeneousMatrix.fullLevel P n) hDense
  let x : HeterogeneousLevelTuple P 0 :=
    Classical.choice
      (inferInstance : Nonempty (HeterogeneousLevelTuple P 0))
  obtain ⟨y, hy, _⟩ := hProduct x
  simpa using hy.1

end GeneralTree
end Milliken
