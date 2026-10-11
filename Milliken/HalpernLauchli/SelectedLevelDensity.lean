import Milliken.HalpernLauchli.SelectedLevelTree

/-!
# Density calculus on a selected-level tree

This ports the elementary Section 3.1 density calculus to the compressed tree
carried by a SelectedLevelTree.Selection. No strong-subtree machinery is
needed here: selected rank n is interpreted simply as ambient level
S.levels n.

In particular this file proves the selected-level analogues of the
observation preceding Lemma 3.5 and of Lemma 3.5 itself. These are the first
pieces of the Chapter 3 induction which survive unchanged when the branching
alphabet is allowed to depend on the level.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- High density measured only at the selected levels. -/
def HighlyDense
    (S : Selection) {d : ℕ}
    (P : Set (Fin d → Node ι)) : Prop :=
  ∀ k : ℕ, ∃ n : ℕ, ∀ M : Matrix ι d,
    M.DenseAt (S.levels n) →
      ProductDenseAt (P ∩ M.carrier) (S.levels k)

/-- HDHL for the selected-level tree. -/
def HDHL
    (S : Selection) (d : ℕ) : Prop :=
  ∀ P : Set (Fin d → Node ι), HighlyDense S P →
    ∀ k : ℕ, 0 < k →
      ∃ M : Matrix ι d,
        M.DenseAt (S.levels k) ∧ M.carrier ⊆ P

/-- A matrix is somewhere dense in the compressed tree. -/
def SomewhereDense
    (S : Selection) {d : ℕ}
    (M : Matrix ι d) : Prop :=
  RestrictedSomewhereDense S.levels M

/-- A set contains a compressed-tree somewhere-dense matrix. -/
def ContainsSomewhereDense
    (S : Selection) {d : ℕ}
    (P : Set (Fin d → Node ι)) : Prop :=
  ContainsRestrictedSomewhereDense S.levels P

/-- Arbitrarily deep cone density above one fixed selected-level vector. -/
def ContainsArbitrarilyDenseAbove
    (S : Selection) {d : ℕ}
    (P : Set (Fin d → Node ι)) : Prop :=
  ∃ p : ℕ, ∃ base : Fin d → Node ι,
    IsLevelVectorAt (S.levels p) base ∧
      ∀ q : ℕ, p < q →
        ∃ M : Matrix ι d,
          M.DenseAbove base (S.levels q) ∧
            M.carrier ⊆ P

/-- If the complement contains no somewhere-dense matrix in the compressed
tree, then the set is highly dense there. As in the book, source level
k+1 works for target level k. -/
theorem highlyDense_of_compl_no_somewhereDense
    [Nonempty ι]
    (S : Selection) {d : ℕ}
    (P : Set (Fin d → Node ι))
    (hno : ¬ ContainsSomewhereDense S Pᶜ) :
    HighlyDense S P := by
  intro k
  refine ⟨k + 1, ?_⟩
  intro M hM
  intro x hx
  by_contra hmiss
  push Not at hmiss
  let N : Matrix ι d := M.restrictAbove x
  have hbase :
      ∀ i, (x i).length < S.levels (k + 1) := by
    intro i
    rw [hx i]
    exact S.strictMono (Nat.lt_succ_self k)
  have hNdense :
      N.DenseAbove x (S.levels (k + 1)) := by
    dsimp [N]
    exact M.restrictAbove_denseAbove x hM hbase
  have hNsub : N.carrier ⊆ Pᶜ := by
    intro y hyN hyP
    have hyM : y ∈ M.carrier :=
      M.restrictAbove_carrier_subset x hyN
    have hpref : ∀ i, (x i).IsPrefix (y i) :=
      M.restrictAbove_prefix x hyN
    rcases hmiss y ⟨hyP, hyM⟩ with ⟨i, hi⟩
    exact hi (hpref i)
  apply hno
  refine ⟨N, ?_, hNsub⟩
  exact ⟨k, k + 1, Nat.lt_succ_self k,
    x, hx, hNdense⟩

/-- Selected-level analogue of Todorčević's Lemma 3.5.

A set is either highly dense in the compressed tree, or its complement has
matrices of arbitrarily large selected density above one fixed selected-level
vector. -/
theorem highlyDense_or_compl_arbitrarilyDense
    [Finite ι] [Nonempty ι]
    (S : Selection) {d : ℕ}
    (P : Set (Fin d → Node ι)) :
    HighlyDense S P ∨
      ContainsArbitrarilyDenseAbove S Pᶜ := by
  classical
  by_cases hP : HighlyDense S P
  · exact Or.inl hP
  · right
    have hfail := hP
    simp only [HighlyDense] at hfail
    push Not at hfail
    rcases hfail with ⟨k, hk⟩
    let badMatrix : ℕ → Matrix ι d := fun r =>
      Classical.choose (hk (k + 1 + r))
    have badMatrix_spec : ∀ r : ℕ,
        (badMatrix r).DenseAt (S.levels (k + 1 + r)) ∧
          ¬ ProductDenseAt
            (P ∩ (badMatrix r).carrier) (S.levels k) := by
      intro r
      exact Classical.choose_spec (hk (k + 1 + r))
    let witness : ℕ → LevelVector ι d (S.levels k) := fun r =>
      Classical.choose
        (exists_bad_levelVector P (badMatrix r)
          (badMatrix_spec r).2)
    have witness_sub : ∀ r : ℕ,
        ((badMatrix r).restrictAbove (witness r).1).carrier ⊆
          Pᶜ := by
      intro r
      exact Classical.choose_spec
        (exists_bad_levelVector P (badMatrix r)
          (badMatrix_spec r).2)
    have hwitness : ∀ r : ℕ,
        ∃ M : Matrix ι d,
          M.DenseAbove (witness r).1
              (S.levels (k + 1 + r)) ∧
            M.carrier ⊆ Pᶜ := by
      intro r
      let N : Matrix ι d :=
        (badMatrix r).restrictAbove (witness r).1
      have hbase :
          ∀ i, ((witness r).1 i).length <
            S.levels (k + 1 + r) := by
        intro i
        rw [(witness r).2 i]
        exact S.strictMono (by omega)
      refine ⟨N, ?_, ?_⟩
      · dsimp [N]
        exact (badMatrix r).restrictAbove_denseAbove
          (witness r).1 (badMatrix_spec r).1 hbase
      · dsimp [N]
        exact witness_sub r
    letI : Finite (LevelVector ι d (S.levels k)) :=
      finite_levelVector d (S.levels k)
    rcases Finite.exists_infinite_fiber witness with
      ⟨base, hbaseInf⟩
    have hfiber : Set.Infinite (witness ⁻¹' {base}) :=
      Set.infinite_coe_iff.mp hbaseInf
    refine ⟨k, base.1, base.2, ?_⟩
    intro q hkq
    obtain ⟨r, hrmem, hqr⟩ := hfiber.exists_gt q
    have hrbase : witness r = base := by
      simpa using hrmem
    rcases hwitness r with ⟨M, hMdense, hMsub⟩
    rw [hrbase] at hMdense
    have hqindex : q ≤ k + 1 + r := by omega
    have hqlevel :
        S.levels q ≤ S.levels (k + 1 + r) :=
      S.strictMono.monotone hqindex
    exact ⟨M, M.denseAbove_of_le hqlevel hMdense, hMsub⟩

/-- The selected-level asymmetric dichotomy obtained from selected HDHL. -/
theorem asymmetric_of_hdhl
    [Finite ι] [Nonempty ι]
    (S : Selection) {d : ℕ}
    (hHDHL : HDHL (ι := ι) S d)
    (K0 : Set (Fin d → Node ι)) :
    (∀ k : ℕ, 0 < k →
      ∃ M : Matrix ι d,
        M.DenseAt (S.levels k) ∧ M.carrier ⊆ K0) ∨
    ContainsArbitrarilyDenseAbove S K0ᶜ := by
  rcases highlyDense_or_compl_arbitrarilyDense S K0 with
    hK0 | hbad
  · left
    intro k hk
    exact hHDHL K0 hK0 k hk
  · exact Or.inr hbad

/-- Selected HDHL immediately gives the reduced selected-level dichotomy. -/
theorem restrictedReduced_of_hdhl
    [Finite ι] [Nonempty ι]
    (S : Selection) {d : ℕ}
    (hHDHL : HDHL (ι := ι) S d) :
    RestrictedReducedDichotomy ι d S.levels := by
  intro P hno
  have hP : HighlyDense S P :=
    highlyDense_of_compl_no_somewhereDense S P hno
  rcases hHDHL P hP 1 (by omega) with
    ⟨M, hMdense, hMsub⟩
  exact ⟨M, hMdense, hMsub⟩

end SelectedLevelTree
end HalpernLauchli
end Milliken
