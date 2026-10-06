import Milliken.HalpernLauchli.Lemma316
import Milliken.HalpernLauchli.SparseFiniteHL

/-!
# A fixed base with arbitrarily dense monochromatic level matrices

This is the strengthening of binary SDHL used in Todorčević's proof of
Theorem 3.2.  For a binary coloring of a finite product, there is one
level-vector `base` such that above `base` one can find monochromatic
level matrices at every prescribed density scale.

The book proves this by contradiction, choosing a sparse sequence of levels
which outruns the obstruction attached to every base on the preceding
selected level, then applying finite Halpern--Läuchli to the sparse trees.
Here the same argument is expressed using `sparseFiniteHL_of_hdhl`.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A level matrix of one color, dense above a prescribed base. -/
def LevelMonochromaticAbove {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι) (q : ℕ) : Prop :=
  ∃ color : Fin 2, ∃ M : Matrix ι d, ∃ l : ℕ,
    M.OnLevel l ∧
      M.DenseAbove base q ∧
      ∀ x ∈ M.carrier, c x = color

/-- Global density is density above the root vector. -/
theorem Matrix.denseAbove_nil_of_denseAt
    {d q : ℕ} (M : Matrix ι d)
    (hM : M.DenseAt q) :
    M.DenseAbove (fun _ => ([] : Node ι)) q := by
  intro i s hs
  rcases hM i hs.2 with ⟨y, hy, hsy⟩
  exact ⟨y, hy, hsy⟩

/-- Failure of the fixed-base conclusion gives one forbidden density scale
for every level-vector. -/
theorem exists_bad_monochromatic_scale
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) (x : LevelVector ι d n) :
    ∃ q : ℕ, ¬ LevelMonochromaticAbove c x.1 q := by
  by_contra h
  push Not at h
  exact hfail ⟨x.1, ⟨n, x.2⟩, h⟩

/-- Choose the first density scale at which a given base fails. -/
noncomputable def badMonochromaticScale
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) (x : LevelVector ι d n) : ℕ :=
  Classical.choose (exists_bad_monochromatic_scale c hfail n x)

theorem badMonochromaticScale_spec
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) (x : LevelVector ι d n) :
    ¬ LevelMonochromaticAbove c x.1
      (badMonochromaticScale c hfail n x) :=
  Classical.choose_spec
    (exists_bad_monochromatic_scale c hfail n x)

/-- One sparse-level successor.  It is above the previous level and above
all bad scales attached to bases on that level. -/
noncomputable def nextMonochromaticLevel
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) : ℕ := by
  classical
  letI : Finite (LevelVector ι d n) :=
    finite_levelVector d n
  letI : Fintype (LevelVector ι d n) :=
    Fintype.ofFinite _
  exact max (n + 1)
    (1 + Finset.univ.sup
      (badMonochromaticScale c hfail n))

/-- The recursively chosen sparse levels from the proof of Theorem 3.2. -/
noncomputable def monochromaticSparseLevels
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    ℕ → ℕ
  | 0 => 0
  | p + 1 =>
      nextMonochromaticLevel c hfail
        (monochromaticSparseLevels c hfail p)

theorem nextMonochromaticLevel_gt
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) :
    n < nextMonochromaticLevel c hfail n := by
  classical
  unfold nextMonochromaticLevel
  exact lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_max_left _ _)

theorem badMonochromaticScale_lt_next
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) (x : LevelVector ι d n) :
    badMonochromaticScale c hfail n x <
      nextMonochromaticLevel c hfail n := by
  classical
  letI : Finite (LevelVector ι d n) :=
    finite_levelVector d n
  letI : Fintype (LevelVector ι d n) :=
    Fintype.ofFinite _
  have hle :
      badMonochromaticScale c hfail n x ≤
        Finset.univ.sup (badMonochromaticScale c hfail n) :=
    Finset.le_sup (f := badMonochromaticScale c hfail n)
      (Finset.mem_univ x)
  unfold nextMonochromaticLevel
  have hsucc :
      badMonochromaticScale c hfail n x <
        1 + Finset.univ.sup
          (badMonochromaticScale c hfail n) := by
    omega
  exact hsucc.trans_le (Nat.le_max_right _ _)

theorem monochromaticSparseLevels_strictMono
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    StrictMono (monochromaticSparseLevels c hfail) := by
  apply strictMono_nat_of_lt_succ
  intro p
  exact nextMonochromaticLevel_gt c hfail
    (monochromaticSparseLevels c hfail p)

theorem monochromaticSparseLevels_unbounded
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    ∀ r : ℕ, ∃ p : ℕ,
      r ≤ monochromaticSparseLevels c hfail p :=
  nat_strictMono_unbounded _
    (monochromaticSparseLevels_strictMono c hfail)

/-- Every obstruction at selected level `p` is outrun by selected level
`p+1`. -/
theorem badScale_lt_sparse_succ
    [Finite ι]
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (hfail :
      ¬ ∃ base : Fin d → Node ι,
          IsLevelVector base ∧
            ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (p : ℕ)
    (x : LevelVector ι d
      (monochromaticSparseLevels c hfail p)) :
    badMonochromaticScale c hfail
        (monochromaticSparseLevels c hfail p) x <
      monochromaticSparseLevels c hfail (p + 1) := by
  exact badMonochromaticScale_lt_next c hfail
    (monochromaticSparseLevels c hfail p) x

/-- Binary HDHL supplies the fixed base needed for the strong-subtree
construction: above one level-vector there are monochromatic level matrices
at every density scale. -/
theorem exists_base_levelMonochromaticAbove
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (c : (Fin d → Node ι) → Fin 2) :
    ∃ base : Fin d → Node ι,
      IsLevelVector base ∧
        ∀ q : ℕ, LevelMonochromaticAbove c base q := by
  classical
  by_contra hfail
  let levels : ℕ → ℕ :=
    monochromaticSparseLevels c hfail
  have hlevels : StrictMono levels := by
    dsimp [levels]
    exact monochromaticSparseLevels_strictMono c hfail
  have hunbounded :
      ∀ r : ℕ, ∃ p : ℕ, r ≤ levels p := by
    dsimp [levels]
    exact monochromaticSparseLevels_unbounded c hfail
  have hk : 0 < levels 1 := by
    change 0 < nextMonochromaticLevel c hfail 0
    exact nextMonochromaticLevel_gt c hfail 0
  rcases sparseFiniteHL_of_hdhl
      hHDHL hk hlevels hunbounded with
    ⟨L, hfinite⟩
  let Full : Matrix ι d := Matrix.fullLevel L
  have hFull : Full.DenseAt L := by
    dsimp [Full]
    exact Matrix.fullLevel_dense (ι := ι) (d := d) L
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  rcases hfinite Full hFull K0 with hone | hzero
  · rcases hone with ⟨N, hNsparse, hNsub⟩
    rcases hNsparse with ⟨p, base, hbase, hNdense⟩
    let x : LevelVector ι d (levels p) :=
      ⟨base, hbase⟩
    have hbad :
        badMonochromaticScale c hfail (levels p) x <
          levels (p + 1) := by
      dsimp [levels]
      exact badScale_lt_sparse_succ c hfail p x
    have hNnonempty :
        ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAbove base hNdense
        (fun i => by
          rw [hbase i]
          exact Nat.le_of_lt (hlevels (Nat.lt_succ_self p)))
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel L := by
      apply N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
      · dsimp [Full]
        exact Matrix.fullLevel_onLevel (ι := ι) (d := d) L
      · exact hNnonempty
    have hNdenseBad :
        N.DenseAbove base
          (badMonochromaticScale c hfail (levels p) x) :=
      N.denseAbove_of_le (Nat.le_of_lt hbad) hNdense
    have hmono :
        ∀ z ∈ N.carrier, c z = (1 : Fin 2) := by
      intro z hz
      have hz1 : z ∈ K0ᶜ := (hNsub hz).2
      apply Fin.eq_one_of_ne_zero
      intro hz0
      exact hz1 hz0
    exact
      (badMonochromaticScale_spec c hfail (levels p) x)
        ⟨1, N, L, hNlevel, hNdenseBad, hmono⟩
  · rcases hzero with ⟨N, hNdense, hNsub⟩
    let base : Fin d → Node ι := fun _ => []
    have hbase : IsLevelVectorAt (levels 0) base := by
      intro i
      simp [levels, monochromaticSparseLevels, base]
    let x : LevelVector ι d (levels 0) :=
      ⟨base, hbase⟩
    have hbad :
        badMonochromaticScale c hfail (levels 0) x <
          levels 1 := by
      dsimp [levels]
      exact badScale_lt_sparse_succ c hfail 0 x
    have hNnonempty :
        ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAt hNdense
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel L := by
      apply N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
      · dsimp [Full]
        exact Matrix.fullLevel_onLevel (ι := ι) (d := d) L
      · exact hNnonempty
    have hNdenseBad :
        N.DenseAt
          (badMonochromaticScale c hfail (levels 0) x) :=
      N.denseAt_of_le (Nat.le_of_lt hbad) hNdense
    have hNabove :
        N.DenseAbove base
          (badMonochromaticScale c hfail (levels 0) x) :=
      N.denseAbove_nil_of_denseAt hNdenseBad
    have hmono :
        ∀ z ∈ N.carrier, c z = (0 : Fin 2) := by
      intro z hz
      exact (hNsub hz).2
    exact
      (badMonochromaticScale_spec c hfail (levels 0) x)
        ⟨0, N, L, hNlevel, hNabove, hmono⟩

end HalpernLauchli
end Milliken
