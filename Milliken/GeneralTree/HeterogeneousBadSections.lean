import Milliken.GeneralTree.HeterogeneousStabilization
import Milliken.GeneralTree.HeterogeneousAsymmetric

/-!
# Bad last-coordinate sections in the heterogeneous HDHL induction

This is the actual locally finitely branching tree version of
Todorčević's first reduction in Lemma 3.15. A last-coordinate node y
is bad at scale n when an n-dense level matrix has a section in
which k-product density fails.

A failure exposes a level-k tuple whose coordinatewise successor
cones support a level matrix avoiding that entire section.
The witness is obtained from the already-verified heterogeneous
asymmetric density reduction, not from a homogeneous fixed alphabet.

All statements here are unconditional elementary reductions.
They are not the still-unproved multi-coordinate HDHL theorem.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A last-coordinate section is bad at scale n for density target k
when a level-supported n-dense front-coordinate matrix fails to be
k-product dense in that section. -/
def HeterogeneousBadSectionAt
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k n : ℕ) (y : U) : Prop :=
  ∃ M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc),
    M.LevelDenseAt n ∧
      ¬ HeterogeneousProductDenseAt
        (fun i : Fin d => P i.castSucc)
        (heterogeneousLastSection Q y ∩ M.carrier) k

/-- An avoiding witness at base tuple base and scale n,
supported on a common source level of the actual front trees. -/
def HeterogeneousSectionAvoidAt
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (y : U) (base : Fin d → U) (n : ℕ) : Prop :=
  ∃ M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc),
    ∃ l : ℕ,
      M.OnLevel l ∧
      M.DenseAbove base n ∧
      M.carrier ⊆ (heterogeneousLastSection Q y)ᶜ

/-- Every bad section at scale n provides an avoiding cone
above one genuine finite level-k tuple of its front factors. -/
theorem heterogeneousBadSectionAt_has_avoidWitness
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    {k n : ℕ} (_hkn : k < n)
    {y : U}
    (hbad : HeterogeneousBadSectionAt P Q k n y) :
    ∃ x : HeterogeneousLevelTuple
        (fun i : Fin d => P i.castSucc) k,
      HeterogeneousSectionAvoidAt P Q y x.1 n := by
  obtain ⟨M, ⟨l, hLevel, hDense⟩, hfail⟩ := hbad
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  obtain ⟨x, hxAvoid⟩ :=
    exists_bad_heterogeneous_levelTuple
      Front (heterogeneousLastSection Q y) M k hfail
  let N := M.restrictAbove x.1
  refine ⟨x, N, l, ?_, ?_, hxAvoid⟩
  · intro i z hz
    exact hLevel i z hz.1
  · exact M.restrictAbove_denseAbove x.1 n hDense

/-- Badness is monotone downward in the density scale. -/
theorem heterogeneousBadSectionAt_of_le
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {m n : ℕ} (hmn : m ≤ n) (y : U)
    (hbad : HeterogeneousBadSectionAt P Q k n y) :
    HeterogeneousBadSectionAt P Q k m y := by
  obtain ⟨M, ⟨l, hLevel, hDense⟩, hFail⟩ := hbad
  exact ⟨M, ⟨l, hLevel, M.denseAt_of_le hmn hDense⟩, hFail⟩

/-- An avoiding witness remains valid at an earlier density scale. -/
theorem heterogeneousSectionAvoidAt_of_le
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (y : U) (base : Fin d → U)
    {m n : ℕ} (hmn : m ≤ n)
    (h : HeterogeneousSectionAvoidAt P Q y base n) :
    HeterogeneousSectionAvoidAt P Q y base m := by
  obtain ⟨M, l, hLevel, hDense, hAvoid⟩ := h
  exact ⟨M, l, hLevel,
    M.denseAbove_of_le base hmn hDense, hAvoid⟩

/-- A family of last-coordinate sections is good when every
n-level-dense front matrix is k-product dense in each section. -/
def HeterogeneousSectionsGoodAt
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k n : ℕ) (Y : Set U) : Prop :=
  ∀ y ∈ Y, ∀ M : HeterogeneousMatrix
    (fun i : Fin d => P i.castSucc),
    M.LevelDenseAt n →
      HeterogeneousProductDenseAt
        (fun i : Fin d => P i.castSucc)
        (heterogeneousLastSection Q y ∩ M.carrier) k

/-- Goodness is precisely the absence of bad sections. -/
theorem heterogeneousSectionsGoodAt_iff
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k n : ℕ) (Y : Set U) :
    HeterogeneousSectionsGoodAt P Q k n Y ↔
      ∀ y ∈ Y, ¬ HeterogeneousBadSectionAt P Q k n y := by
  constructor
  · intro hgood y hy hbad
    obtain ⟨M, hM, hnot⟩ := hbad
    exact hnot (hgood y hy M hM)
  · intro hno y hy M hM
    by_contra hbad
    exact hno y hy ⟨M, hM, hbad⟩

end GeneralTree
end Milliken
