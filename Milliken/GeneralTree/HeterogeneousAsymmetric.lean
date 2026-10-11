import Milliken.GeneralTree.HeterogeneousObstruction
import Mathlib.Data.Fintype.Pigeonhole

/-!
# The heterogeneous asymmetric density dichotomy of Todorčević §3.2

If a colour class Q is not highly dense, for one fixed selected
source index k and arbitrarily high test indices there are dense
matrices which fail product density in Q. Each failure yields a
specific level-k tuple whose entire coordinate-cone restriction
misses Q. Because the kth source-level product is finite, one
such tuple recurs infinitely often. The associated bad-cone
matrices are therefore dense above *one fixed base tuple* at
arbitrarily high scales.

Combined with the actual-tree HDHL conclusion (once proved in
the requested dimension), this gives Todorčević's asymmetric
two-colour density dichotomy.

This is the exact argument for products of arbitrary locally
finitely branching rooted trees, not an appeal to a fixed
alphabet or uniform branching bound. No heterogeneous HL theorem
is assumed in the purely combinatorial first implication.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}
variable (P : Fin d → StrongSubtree U)

/-- Failure of product density exposes a level-k tuple whose
entire coordinatewise cone restriction of M misses Q. -/
theorem exists_bad_heterogeneous_levelTuple
    (Q : Set (Fin d → U))
    (M : HeterogeneousMatrix P) (k : ℕ)
    (hnot :
      ¬ HeterogeneousProductDenseAt P (Q ∩ M.carrier) k) :
    ∃ base : HeterogeneousLevelTuple P k,
      (M.restrictAbove base.1).carrier ⊆ Qᶜ := by
  classical
  have hex :
      ∃ base : HeterogeneousLevelTuple P k,
        ¬ ∃ y : Fin d → U,
          y ∈ Q ∩ M.carrier ∧
            ∀ i, base.1 i ≤ y i := by
    by_contra hnone
    apply hnot
    intro base
    by_contra hnoneBase
    exact hnone ⟨base, hnoneBase⟩
  obtain ⟨base, hbaseBad⟩ := hex
  refine ⟨base, ?_⟩
  intro y hy hQ
  have hM : y ∈ M.carrier :=
    M.restrictAbove_carrier_subset base.1 hy
  have hle : ∀ i, base.1 i ≤ y i :=
    fun i => (hy i).2
  exact hbaseBad ⟨y, ⟨hQ, hM⟩, hle⟩

/-- Failure of high density produces arbitrarily dense
complement-colour matrices above one fixed source-level tuple.
This is the source-faithful heterogeneous alternative of
Todorčević's Lemma 3.5 and the preceding density dichotomy. -/
theorem heterogeneousHighlyDense_or_compl_arbitrarilyDense
    (Q : Set (Fin d → U)) :
    HeterogeneousHighlyDense P Q ∨
      HeterogeneousContainsArbitrarilyDenseAbove P Qᶜ := by
  classical
  by_cases hQ : HeterogeneousHighlyDense P Q
  · exact Or.inl hQ
  · right
    have hfail :
        ∃ k : ℕ, ∀ n : ℕ,
          ∃ M : HeterogeneousMatrix P,
            M.DenseAt n ∧
              ¬ HeterogeneousProductDenseAt
                P (Q ∩ M.carrier) k := by
      unfold HeterogeneousHighlyDense at hQ
      push_neg at hQ
      exact hQ
    obtain ⟨k, hk⟩ := hfail
    let badMatrix : ℕ → HeterogeneousMatrix P :=
      fun r => Classical.choose (hk (k + 1 + r))
    have badMatrix_spec (r : ℕ) :
        (badMatrix r).DenseAt (k + 1 + r) ∧
          ¬ HeterogeneousProductDenseAt
            P (Q ∩ (badMatrix r).carrier) k :=
      Classical.choose_spec (hk (k + 1 + r))
    let witness : ℕ → HeterogeneousLevelTuple P k :=
      fun r => Classical.choose
        (exists_bad_heterogeneous_levelTuple
          P Q (badMatrix r) k (badMatrix_spec r).2)
    have witness_sub (r : ℕ) :
        ((badMatrix r).restrictAbove (witness r).1).carrier ⊆
          Qᶜ :=
      Classical.choose_spec
        (exists_bad_heterogeneous_levelTuple
          P Q (badMatrix r) k (badMatrix_spec r).2)
    have hwitness (r : ℕ) :
        ∃ M : HeterogeneousMatrix P,
          M.DenseAbove (witness r).1 (k + 1 + r) ∧
            M.carrier ⊆ Qᶜ := by
      let M := (badMatrix r).restrictAbove (witness r).1
      refine ⟨M, ?_, witness_sub r⟩
      exact (badMatrix r).restrictAbove_denseAbove
        (witness r).1 (k + 1 + r)
        (badMatrix_spec r).1
    letI : Finite (HeterogeneousLevelTuple P k) :=
      heterogeneousLevelTuple_finite P k
    obtain ⟨base, hbaseInf⟩ :=
      Finite.exists_infinite_fiber witness
    have hfiber : Set.Infinite (witness ⁻¹' {base}) :=
      Set.infinite_coe_iff.mp hbaseInf
    refine ⟨base.1, (fun i => (base.2 i).1), ?_⟩
    intro q
    obtain ⟨r, hrmem, hqr⟩ := hfiber.exists_gt q
    have hrbase : witness r = base := by
      simpa using hrmem
    obtain ⟨M, hMdense, hMbad⟩ := hwitness r
    refine ⟨M, ?_, hMbad⟩
    rw [hrbase] at hMdense
    exact M.denseAbove_of_le base.1
      (by omega : q ≤ k + 1 + r) hMdense

/-- Todorčević's asymmetric colour dichotomy for genuinely
heterogeneous tree products, assuming *only* heterogeneous
HDHL in the current dimension. This is the induction-ready
counterpart of the homogeneous asymmetric_of_hdhl theorem. -/
theorem heterogeneousAsymmetric_of_hdhl
    (hHDHL : HasHeterogeneousHDHL P)
    (Q : Set (Fin d → U)) :
    (∀ k : ℕ, 0 < k →
      ∃ M : HeterogeneousMatrix P,
        M.DenseAt k ∧ M.carrier ⊆ Q) ∨
      HeterogeneousContainsArbitrarilyDenseAbove P Qᶜ := by
  rcases heterogeneousHighlyDense_or_compl_arbitrarilyDense
      P Q with hhigh | hbad
  · left
    intro k hk
    exact hHDHL Q hhigh k hk
  · exact Or.inr hbad

end GeneralTree
end Milliken
