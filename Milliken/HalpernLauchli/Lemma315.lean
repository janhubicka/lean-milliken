import Milliken.HalpernLauchli.Sections
import Milliken.HalpernLauchli.Asymmetric

/-!
# The logical shell of Lemma 3.15

For fixed P and k, call y bad at scale n if some n-dense level matrix M
has P_y ∩ M failing k-density.  If the conclusion of Lemma 3.15 fails,
then at every n the good part of X cannot itself be somewhere cone-dense.
This is the first reduction in Todorčević's proof; the later minimal-D
argument uses only the resulting bad sets.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A last-coordinate node is bad at scale n when some level n-dense
matrix has a non-k-dense intersection with its section. -/
def BadSectionAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (y : Node ι) : Prop :=
  ∃ M : Matrix ι d,
    M.LevelDenseAt n ∧
      ¬ ProductDenseAt (lastSection P y ∩ M.carrier) k

/-- A level matrix avoiding one section while remaining dense above a fixed
front-coordinate vector.  This is the witness appearing in (1)--(3) of the
proof of Lemma 3.15. -/
def SectionAvoidAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (y : Node ι) (base : Fin d → Node ι) (n : ℕ) : Prop :=
  ∃ M : Matrix ι d, ∃ l : ℕ,
    M.OnLevel l ∧
    M.DenseAbove base n ∧
    M.carrier ⊆ (lastSection P y)ᶜ

theorem sectionAvoidAt_of_le [Nonempty ι] {d : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    {y : Node ι} {base : Fin d → Node ι}
    {m n : ℕ} (hmn : m ≤ n)
    (h : SectionAvoidAt P y base n) :
    SectionAvoidAt P y base m := by
  rcases h with ⟨M, l, hlevel, hdense, hsub⟩
  exact ⟨M, l, hlevel, M.denseAbove_of_le hmn hdense, hsub⟩

/-- Failure of k-density inside an n-dense level matrix exposes a single
level-k vector above which a level matrix misses the entire section. -/
theorem badSectionAt_has_avoidWitness [Nonempty ι] {d k n : ℕ}
    {P : Set (Fin (d + 1) → Node ι)} {y : Node ι}
    (hkn : k < n)
    (hbad : BadSectionAt P k n y) :
    ∃ x : LevelVector ι d k,
      SectionAvoidAt P y x.1 n := by
  rcases hbad with ⟨M, ⟨l, hlevel, hdense⟩, hfail⟩
  rcases exists_bad_levelVector (lastSection P y) M hfail with
    ⟨x, hxsub⟩
  have hbase : ∀ i, (x.1 i).length < n := by
    intro i
    rw [x.2 i]
    exact hkn
  let N : Matrix ι d := M.restrictAbove x.1
  refine ⟨x, N, l, ?_, ?_, ?_⟩
  · dsimp [N]
    exact M.restrictAbove_onLevel hlevel
  · dsimp [N]
    exact M.restrictAbove_denseAbove x.1 hdense hbase
  · dsimp [N]
    exact hxsub

/-- Badness itself is downward monotone in the density level. -/
theorem badSectionAt_of_le [Nonempty ι] {d k : ℕ}
    {P : Set (Fin (d + 1) → Node ι)} {y : Node ι}
    {m n : ℕ} (hmn : m ≤ n)
    (hbad : BadSectionAt P k n y) :
    BadSectionAt P k m y := by
  rcases hbad with ⟨M, hM, hfail⟩
  exact ⟨M, M.levelDenseAt_of_le hmn hM, hfail⟩

/-- Bad nodes restricted to a prescribed set X. -/
def badSectionSet {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (X : Set (Node ι)) : Set (Node ι) :=
  X ∩ {y | BadSectionAt P k n y}

/-- The desired uniform conclusion at fixed n on Y. -/
def SectionsGoodAt {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (Y : Set (Node ι)) : Prop :=
  ∀ y ∈ Y, ∀ M : Matrix ι d,
    M.LevelDenseAt n →
      ProductDenseAt (lastSection P y ∩ M.carrier) k

theorem sectionsGoodAt_iff_no_bad {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k n : ℕ) (Y : Set (Node ι)) :
    SectionsGoodAt P k n Y ↔
      ∀ y ∈ Y, ¬ BadSectionAt P k n y := by
  constructor
  · intro h y hy hbad
    rcases hbad with ⟨M, hM, hfail⟩
    exact hfail (h y hy M hM)
  · intro h y hy M hM
    by_contra hfail
    exact h y hy ⟨M, hM, hfail⟩

/-- If no n,Y satisfy the conclusion of Lemma 3.15, then for each n the
good part of X is not somewhere cone-dense. -/
theorem good_complement_not_somewhere_of_no_uniform {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) (X : Set (Node ι))
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set (Node ι),
        Y ⊆ X ∧ SomewhereConeDense Y ∧ SectionsGoodAt P k n Y) :
    ∀ n : ℕ,
      ¬ SomewhereConeDense
        (X \ badSectionSet P k n X) := by
  intro n hsome
  let Y : Set (Node ι) := X \ badSectionSet P k n X
  have hYX : Y ⊆ X := by
    intro y hy
    exact hy.1
  have hgood : SectionsGoodAt P k n Y := by
    rw [sectionsGoodAt_iff_no_bad]
    intro y hyY hbad
    exact hyY.2 ⟨hyY.1, hbad⟩
  exact hfail ⟨n, Y, hYX, hsome, hgood⟩

/-- Equivalently, under failure of the uniform conclusion every somewhere
dense subset of X contains a bad node at every scale. -/
theorem exists_bad_in_somewhere_of_no_uniform {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (k : ℕ) (X : Set (Node ι))
    (hfail :
      ¬ ∃ n : ℕ, ∃ Y : Set (Node ι),
        Y ⊆ X ∧ SomewhereConeDense Y ∧ SectionsGoodAt P k n Y)
    (n : ℕ) {Y : Set (Node ι)}
    (hYX : Y ⊆ X) (hY : SomewhereConeDense Y) :
    ∃ y ∈ Y, BadSectionAt P k n y := by
  by_contra hnone
  push Not at hnone
  have hsub :
      Y ⊆ X \ badSectionSet P k n X := by
    intro y hy
    refine ⟨hYX hy, ?_⟩
    intro hybad
    exact hnone y hy hybad.2
  have hsome :
      SomewhereConeDense (X \ badSectionSet P k n X) :=
    somewhereConeDense_mono hsub hY
  exact good_complement_not_somewhere_of_no_uniform P k X hfail n hsome

end HalpernLauchli
end Milliken
