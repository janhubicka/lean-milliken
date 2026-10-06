import Milliken.HalpernLauchli.Density
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.List

/-!
# The asymmetric density dichotomy

This file formalizes Todorčević's Lemma 3.5 in the homogeneous tree
presentation.  If a set is not highly dense, choose for every sufficiently
large level an n-dense matrix witnessing failure.  Each failure exposes a
level-k vector above which the matrix misses the set.  There are only finitely
many level-k vectors, so one vector occurs for infinitely many n.  Those
restricted matrices witness arbitrary k-x density in the complement.
-/

namespace Milliken
namespace HalpernLauchli

universe u

variable {ι : Type u}

/-- Level vectors at a fixed level, packaged as a finite type. -/
def LevelVector (ι : Type u) (d k : ℕ) :=
  {x : Fin d → Node ι // IsLevelVectorAt k x}

theorem finite_levelVector [Finite ι] (d k : ℕ) :
    Finite (LevelVector ι d k) := by
  letI : Finite {s : Node ι // s.length = k} :=
    (List.finite_length_eq ι k).to_subtype
  let encode : LevelVector ι d k →
      (Fin d → {s : Node ι // s.length = k}) :=
    fun x i => ⟨x.1 i, x.2 i⟩
  apply Finite.of_injective encode
  intro x y hxy
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

/-- Fix one letter, used only to pad a node to a prescribed later level. -/
noncomputable def padLetter (ι : Type u) [Nonempty ι] : ι :=
  Classical.choice (inferInstance : Nonempty ι)

/-- Extend a node to level n by a constant tail. -/
noncomputable def extendToLevel (s : Node ι) (n : ℕ) [Nonempty ι] :
    Node ι :=
  s ++ List.replicate (n - s.length) (padLetter ι)

theorem prefix_extendToLevel [Nonempty ι] (s : Node ι) (n : ℕ) :
    s.IsPrefix (extendToLevel s n) :=
  List.prefix_append _ _

theorem length_extendToLevel [Nonempty ι] {s : Node ι} {n : ℕ}
    (hsn : s.length ≤ n) :
    (extendToLevel s n).length = n := by
  simp [extendToLevel, hsn, Nat.add_sub_of_le]

/-- Density at a later level implies density at every earlier level. -/
theorem Matrix.denseAt_of_le [Nonempty ι] {d : ℕ}
    {M : Matrix ι d} {m n : ℕ}
    (hmn : m ≤ n) (hM : M.DenseAt n) :
    M.DenseAt m := by
  intro i t ht
  have htm : t.length = m := ht
  have hlen : t.length ≤ n := by omega
  let u : Node ι := extendToLevel t n
  have htu : t.IsPrefix u := prefix_extendToLevel t n
  have hulen : u.length = n := length_extendToLevel hlen
  rcases hM i
      (show u ∈ treeLevel (ι := ι) n from hulen) with
    ⟨y, hyM, huy⟩
  exact ⟨y, hyM, htu.trans huy⟩

/-- The level-matrix strengthening is likewise downward monotone. -/
theorem Matrix.levelDenseAt_of_le [Nonempty ι] {d : ℕ}
    {M : Matrix ι d} {m n : ℕ}
    (hmn : m ≤ n) (hM : M.LevelDenseAt n) :
    M.LevelDenseAt m := by
  rcases hM with ⟨l, hlevel, hdense⟩
  exact ⟨l, hlevel, M.denseAt_of_le hmn hdense⟩

/-- Density above a base at a later level implies density above the same
base at every earlier level.  Levels below the base are vacuous. -/
theorem Matrix.denseAbove_of_le [Nonempty ι] {d : ℕ}
    {M : Matrix ι d} {base : Fin d → Node ι} {m n : ℕ}
    (hmn : m ≤ n) (hM : M.DenseAbove base n) :
    M.DenseAbove base m := by
  intro i t ht
  have htm : t.length = m := ht.2
  have hlen : t.length ≤ n := by omega
  let u : Node ι := extendToLevel t n
  have htu : t.IsPrefix u := prefix_extendToLevel t n
  have hulen : u.length = n := length_extendToLevel hlen
  have hbaseu : (base i).IsPrefix u := ht.1.trans htu
  rcases hM i
      (show u ∈ coneLevel (base i) n from ⟨hbaseu, hulen⟩) with
    ⟨y, hyM, huy⟩
  exact ⟨y, hyM, htu.trans huy⟩

/-- Negating product density produces a level vector whose cone misses the
set inside the given matrix. -/
theorem exists_bad_levelVector {d k : ℕ}
    (P : Set (Fin d → Node ι)) (M : Matrix ι d)
    (hbad : ¬ ProductDenseAt (P ∩ M.carrier) k) :
    ∃ x : LevelVector ι d k,
      (M.restrictAbove x.1).carrier ⊆ Pᶜ := by
  simp only [ProductDenseAt] at hbad
  push Not at hbad
  rcases hbad with ⟨x, hxlevel, hmiss⟩
  refine ⟨⟨x, hxlevel⟩, ?_⟩
  intro y hyN hyP
  have hyM : y ∈ M.carrier :=
    M.restrictAbove_carrier_subset x hyN
  have hpref : ∀ i, (x i).IsPrefix (y i) :=
    M.restrictAbove_prefix x hyN
  rcases hmiss y ⟨hyP, hyM⟩ with ⟨i, hi⟩
  exact hi (hpref i)

/-- Todorčević's Lemma 3.5.

Either P is highly dense, or there is one level vector x such that P's
complement contains a q-x-dense matrix for every q. -/
theorem highlyDense_or_compl_denseAbove [Finite ι] [Nonempty ι]
    {d : ℕ} (P : Set (Fin d → Node ι)) :
    HighlyDense P ∨
      ∃ base : Fin d → Node ι,
        IsLevelVector base ∧
        ∀ q : ℕ, ∃ M : Matrix ι d,
          M.DenseAbove base q ∧ M.carrier ⊆ Pᶜ := by
  classical
  by_cases hP : HighlyDense P
  · exact Or.inl hP
  · right
    have hfail := hP
    simp only [HighlyDense] at hfail
    push Not at hfail
    rcases hfail with ⟨k, hk⟩
    let badMatrix : ℕ → Matrix ι d := fun r =>
      Classical.choose (hk (k + 1 + r))
    have badMatrix_spec : ∀ r : ℕ,
        (badMatrix r).DenseAt (k + 1 + r) ∧
          ¬ ProductDenseAt
            (P ∩ (badMatrix r).carrier) k := by
      intro r
      exact Classical.choose_spec (hk (k + 1 + r))
    let witness : ℕ → LevelVector ι d k := fun r =>
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
          M.DenseAbove (witness r).1 (k + 1 + r) ∧
          M.carrier ⊆ Pᶜ := by
      intro r
      let N : Matrix ι d :=
        (badMatrix r).restrictAbove (witness r).1
      have hbase : ∀ i, ((witness r).1 i).length < k + 1 + r := by
        intro i
        rw [(witness r).2 i]
        omega
      refine ⟨N, ?_, ?_⟩
      · dsimp [N]
        exact (badMatrix r).restrictAbove_denseAbove
          (witness r).1 (badMatrix_spec r).1 hbase
      · dsimp [N]
        exact witness_sub r
    letI : Finite (LevelVector ι d k) := finite_levelVector d k
    rcases Finite.exists_infinite_fiber witness with ⟨base, hbaseInf⟩
    have hfiber : Set.Infinite (witness ⁻¹' {base}) :=
      Set.infinite_coe_iff.mp hbaseInf
    refine ⟨base.1, ⟨k, base.2⟩, ?_⟩
    intro q
    obtain ⟨r, hrmem, hqr⟩ := hfiber.exists_gt q
    have hrbase : witness r = base := by
      simpa using hrmem
    rcases hwitness r with ⟨M, hMdense, hMsub⟩
    refine ⟨M, ?_, hMsub⟩
    rw [hrbase] at hMdense
    exact M.denseAbove_of_le (by omega) hMdense

/-- Corollary 3.7, the asymmetric Halpern--Läuchli dichotomy.

Assuming HDHL in dimension d, either the first color contains a k-dense
matrix for every positive k, or one fixed vector has q-vector-dense matrices
of the second color for every q. -/
theorem asymmetric_of_hdhl [Finite ι] [Nonempty ι]
    {d : ℕ} (hHDHL : HDHL ι d)
    (K0 : Set (Fin d → Node ι)) :
    (∀ k : ℕ, 0 < k →
      ∃ M : Matrix ι d, M.DenseAt k ∧ M.carrier ⊆ K0) ∨
    (∃ base : Fin d → Node ι,
      IsLevelVector base ∧
      ∀ q : ℕ, ∃ M : Matrix ι d,
        M.DenseAbove base q ∧ M.carrier ⊆ K0ᶜ) := by
  rcases highlyDense_or_compl_denseAbove K0 with hK0 | hbad
  · left
    intro k hk
    exact hHDHL K0 hK0 k hk
  · exact Or.inr hbad

end HalpernLauchli
end Milliken
