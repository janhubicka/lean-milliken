import Milliken.GeneralTree.HeterogeneousMinimalAvoid

/-!
# Bad sections in every cone under failure of uniform goodness

The logical complement of the first assertion in Todorčević's
Lemma 3.15 says that no cone-dense subfamily of last-coordinate
nodes has uniformly k-dense front sections at any scale.

Under this failure, every cone-dense last-coordinate subfamily
contains a bad section at every test scale. Consequently a
minimum-cardinality avoiding cover cannot be empty.

This step is insensitive to the shape or degree of the actual
tree coordinates. No global branching bound or HL hypothesis
is introduced.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A set of last-coordinate nodes which are bad at one scale. -/
def heterogeneousBadSectionSet
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k n : ℕ) (X : Set U) : Set U :=
  X ∩ {y | HeterogeneousBadSectionAt P Q k n y}

/-- If no cone-dense subset has uniformly good sections at any scale,
then the complement of the bad sections cannot be cone-dense. -/
theorem heterogeneousGoodComplement_not_somewhere
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) (X : Set U)
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set U,
        Y ⊆ X ∧
          HeterogeneousSomewhereConeDense
            (P (Fin.last d)) Y ∧
          HeterogeneousSectionsGoodAt P Q k n Y) :
    ∀ n : ℕ,
      ¬ HeterogeneousSomewhereConeDense
        (P (Fin.last d))
        (X \ heterogeneousBadSectionSet P Q k n X) := by
  intro n hSome
  let Y : Set U :=
    X \ heterogeneousBadSectionSet P Q k n X
  have hYX : Y ⊆ X := fun _ hy => hy.1
  have hGood : HeterogeneousSectionsGoodAt P Q k n Y := by
    apply (heterogeneousSectionsGoodAt_iff P Q k n Y).2
    intro y hyY hBad
    exact hyY.2 ⟨hyY.1, hBad⟩
  exact hfail ⟨n, Y, hYX, hSome, hGood⟩

/-- Every cone-dense subset of X contains a bad section
at every scale when uniform goodness fails. -/
theorem heterogeneousExists_bad_in_somewhere
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) (X : Set U)
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set U,
        Y ⊆ X ∧
          HeterogeneousSomewhereConeDense
            (P (Fin.last d)) Y ∧
          HeterogeneousSectionsGoodAt P Q k n Y)
    (n : ℕ) {Y : Set U}
    (hYX : Y ⊆ X)
    (hSome : HeterogeneousSomewhereConeDense
      (P (Fin.last d)) Y) :
    ∃ y ∈ Y, HeterogeneousBadSectionAt P Q k n y := by
  by_contra hnone
  have hNo : ∀ y ∈ Y,
      ¬ HeterogeneousBadSectionAt P Q k n y := by
    intro y hy hbad
    exact hnone ⟨y, hy, hbad⟩
  have hGood : HeterogeneousSectionsGoodAt P Q k n Y :=
    (heterogeneousSectionsGoodAt_iff P Q k n Y).2 hNo
  exact hfail ⟨n, Y, hYX, hSome, hGood⟩

/-- A minimum avoiding cover under failure of uniform goodness
must contain at least one finite source-level tuple. -/
theorem heterogeneousMinimalAvoidCover_nonempty
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) (X : Set U)
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set U,
        Y ⊆ X ∧
          HeterogeneousSomewhereConeDense
            (P (Fin.last d)) Y ∧
          HeterogeneousSectionsGoodAt P Q k n Y)
    (C : HeterogeneousAvoidCover P Q k X) :
    C.D.Nonempty := by
  classical
  have hSome : HeterogeneousSomewhereConeDense
      (P (Fin.last d)) C.Y :=
    ⟨C.root, C.root_mem, C.Y_dense⟩
  obtain ⟨y, hy, hbad⟩ :=
    heterogeneousExists_bad_in_somewhere
      P Q k X hfail C.n0 C.Y_subset hSome
  obtain ⟨x, hxD, _⟩ := C.cover C.n0 le_rfl y hy hbad
  exact ⟨x, hxD⟩

end GeneralTree
end Milliken
