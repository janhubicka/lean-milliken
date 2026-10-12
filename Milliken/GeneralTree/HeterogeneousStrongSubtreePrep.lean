import Milliken.GeneralTree.HeterogeneousSparseFiniteHL

/-!
# Fixed-base arbitrarily dense monochromatic matrices

This is the heterogeneous version of the strengthening of binary
Halpern--Läuchli used in Todorčević's Theorem 3.2. Given HDHL in a
positive number of actual strong-tree factors and a binary colouring,
there is one level-vector base such that, for every source-index
density target, a common-level monochromatic matrix exists in
the cones above that *same* base.

The proof port follows the homogeneous StrongSubtreePrep argument:
failure assigns a forbidden density target to each finite base;
a recursively chosen sparse source-index sequence outruns all these
targets simultaneously; and the verified sparse finite HL dichotomy
contradicts the assignment.

The coordinate trees may have unrelated roots, non-isomorphic
local branching, and unbounded finite branching across levels.
No fixed alphabet, unknown HL axiom, or extra Ramsey premise occurs.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A binary monochromatic level-supported matrix which is dense
at source index q within the cones above a given coordinate base. -/
def HeterogeneousLevelMonochromaticAbove
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (base : Fin d → U)
    (q : ℕ) : Prop :=
  ∃ color : Fin 2,
    ∃ M : HeterogeneousMatrix P,
      ∃ l : ℕ,
        M.OnLevel l ∧
        M.DenseAbove base q ∧
        ∀ x ∈ M.carrier, c x = color

/-- Failure of a fixed base with arbitrarily dense monochromatic
sections yields an individual forbidden test source index at
every finite product-level base. -/
theorem heterogeneous_exists_bad_monochromatic_scale
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) (base : HeterogeneousLevelTuple P n) :
    ∃ q : ℕ,
      ¬ HeterogeneousLevelMonochromaticAbove P c base.1 q := by
  by_contra h
  have hall :
      ∀ q : ℕ, HeterogeneousLevelMonochromaticAbove P c base.1 q := by
    intro q
    by_contra hq
    exact h ⟨q, hq⟩
  exact hfail ⟨n, base, hall⟩

/-- First chosen density obstruction attached to a source-level tuple. -/
noncomputable def heterogeneousBadMonochromaticScale
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) (base : HeterogeneousLevelTuple P n) : ℕ :=
  Classical.choose
    (heterogeneous_exists_bad_monochromatic_scale P c hfail n base)

theorem heterogeneousBadMonochromaticScale_spec
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) (base : HeterogeneousLevelTuple P n) :
    ¬ HeterogeneousLevelMonochromaticAbove P c base.1
      (heterogeneousBadMonochromaticScale P c hfail n base) :=
  Classical.choose_spec
    (heterogeneous_exists_bad_monochromatic_scale P c hfail n base)

/-- The next test index outruns all obstructions attached to
the finitely many tuples on the current common source level.
Their number depends on the actual tree shapes, not a global bound. -/
noncomputable def heterogeneousNextMonochromaticLevel
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) : ℕ := by
  classical
  letI : Fintype (HeterogeneousLevelTuple P n) :=
    Fintype.ofFinite _
  exact max (n + 1)
    (1 + Finset.univ.sup
      (heterogeneousBadMonochromaticScale P c hfail n))

theorem heterogeneousNextMonochromaticLevel_gt
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) :
    n < heterogeneousNextMonochromaticLevel P c hfail n := by
  classical
  unfold heterogeneousNextMonochromaticLevel
  exact (Nat.lt_succ_self n).trans_le (Nat.le_max_left _ _)

/-- A finite base's forbidden density scale is always strictly
below the next selected source index. -/
theorem heterogeneousBadScale_lt_next
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (n : ℕ) (base : HeterogeneousLevelTuple P n) :
    heterogeneousBadMonochromaticScale P c hfail n base <
      heterogeneousNextMonochromaticLevel P c hfail n := by
  classical
  letI : Fintype (HeterogeneousLevelTuple P n) :=
    Fintype.ofFinite _
  have hsup :
      heterogeneousBadMonochromaticScale P c hfail n base ≤
        Finset.univ.sup
          (heterogeneousBadMonochromaticScale P c hfail n) :=
    Finset.le_sup
      (f := heterogeneousBadMonochromaticScale P c hfail n)
      (Finset.mem_univ base)
  unfold heterogeneousNextMonochromaticLevel
  omega

/-- Recursively chosen source indices avoiding every proposed
fixed-base monochromatic density witness. -/
noncomputable def heterogeneousMonochromaticSparseLevels
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    ℕ → ℕ
  | 0 => 0
  | p + 1 =>
      heterogeneousNextMonochromaticLevel P c hfail
        (heterogeneousMonochromaticSparseLevels P c hfail p)

theorem heterogeneousMonochromaticSparseLevels_strictMono
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    StrictMono (heterogeneousMonochromaticSparseLevels P c hfail) := by
  apply strictMono_nat_of_lt_succ
  intro p
  exact heterogeneousNextMonochromaticLevel_gt P c hfail
    (heterogeneousMonochromaticSparseLevels P c hfail p)

theorem heterogeneousMonochromaticSparseLevels_unbounded
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q) :
    ∀ b : ℕ, ∃ p : ℕ,
      b ≤ heterogeneousMonochromaticSparseLevels P c hfail p := by
  let levels := heterogeneousMonochromaticSparseLevels P c hfail
  have hmono : StrictMono levels :=
    heterogeneousMonochromaticSparseLevels_strictMono P c hfail
  have hdiag : ∀ p : ℕ, p ≤ levels p := by
    intro p
    induction p with
    | zero => omega
    | succ p ih =>
        have hstep : levels p < levels (p + 1) :=
          hmono (Nat.lt_succ_self p)
        omega
  intro b
  exact ⟨b, hdiag b⟩

theorem heterogeneousBadScale_lt_sparse_succ
    (P : Fin d → StrongSubtree U)
    (c : (Fin d → U) → Fin 2)
    (hfail :
      ¬ ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
        ∀ q : ℕ,
          HeterogeneousLevelMonochromaticAbove P c base.1 q)
    (p : ℕ)
    (base : HeterogeneousLevelTuple P
      (heterogeneousMonochromaticSparseLevels P c hfail p)) :
    heterogeneousBadMonochromaticScale P c hfail
        (heterogeneousMonochromaticSparseLevels P c hfail p) base <
      heterogeneousMonochromaticSparseLevels P c hfail (p + 1) :=
  heterogeneousBadScale_lt_next P c hfail
    (heterogeneousMonochromaticSparseLevels P c hfail p) base

/-- A source-level root tuple, available even for factors whose
ambient roots and selected source levels differ. -/
def heterogeneousRootTuple
    (P : Fin d → StrongSubtree U) :
    HeterogeneousLevelTuple P 0 :=
  ⟨fun i => (P i).root,
    fun i => ⟨(P i).root_mem, (P i).root_level⟩⟩

/-- Same-dimensional heterogeneous HDHL implies there is a fixed
front product base above which matrices of one of the two colours
are arbitrarily dense. No a priori choice of the colour is made;
it may depend on the requested scale. -/
theorem heterogeneous_exists_base_levelMonochromaticAbove
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL P)
    (c : (Fin d → U) → Fin 2) :
    ∃ n : ℕ, ∃ base : HeterogeneousLevelTuple P n,
      ∀ q : ℕ,
        HeterogeneousLevelMonochromaticAbove P c base.1 q := by
  classical
  by_contra hfail
  let levels : ℕ → ℕ :=
    heterogeneousMonochromaticSparseLevels P c hfail
  have hlevels : StrictMono levels :=
    heterogeneousMonochromaticSparseLevels_strictMono P c hfail
  have hunbounded : ∀ b : ℕ, ∃ p : ℕ, b ≤ levels p :=
    heterogeneousMonochromaticSparseLevels_unbounded P c hfail
  have hk : 0 < levels 1 := by
    have h := hlevels (show 0 < 1 by omega)
    simpa [levels, heterogeneousMonochromaticSparseLevels] using h
  obtain ⟨L, hfinite⟩ :=
    heterogeneousSparseFiniteHL_of_hdhl
      P hHDHL hk hlevels hunbounded
  let Full : HeterogeneousMatrix P :=
    HeterogeneousMatrix.fullLevel P L
  have hFull : Full.DenseAt L :=
    HeterogeneousMatrix.fullLevel_denseAt P L
  let K0 : Set (Fin d → U) := {x | c x = 0}
  rcases hfinite Full hFull K0 with hone | hzero
  · obtain ⟨N, ⟨p, base, hNdense⟩, hNsub⟩ := hone
    have hbad :
        heterogeneousBadMonochromaticScale P c hfail
          (levels p) base < levels (p + 1) :=
      heterogeneousBadScale_lt_sparse_succ P c hfail p base
    have hNnonempty : ∀ i, (N.coord i).Nonempty := by
      intro i
      have hle : levels p ≤ levels (p + 1) :=
        (hlevels (Nat.lt_succ_self p)).le
      obtain ⟨z, hz, hbasez⟩ :=
        (P i).exists_sourceLevel_descendant hle (base.2 i)
      obtain ⟨w, hw, _⟩ := hNdense i z hz hbasez
      exact ⟨w, hw⟩
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel L :=
      N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
        (HeterogeneousMatrix.fullLevel_onLevel P L) hNnonempty
    have hNbad :
        N.DenseAbove base.1
          (heterogeneousBadMonochromaticScale P c hfail
            (levels p) base) :=
      N.denseAbove_of_le base.1 (Nat.le_of_lt hbad) hNdense
    have hmono : ∀ z ∈ N.carrier, c z = (1 : Fin 2) := by
      intro z hz
      have hzbad : z ∈ K0ᶜ := (hNsub hz).2
      apply Fin.eq_one_of_ne_zero (c z)
      intro heq
      exact hzbad heq
    exact (heterogeneousBadMonochromaticScale_spec
      P c hfail (levels p) base)
        ⟨1, N, L, hNlevel, hNbad, hmono⟩
  · obtain ⟨N, hNdense, hNsub⟩ := hzero
    let root : HeterogeneousLevelTuple P 0 :=
      heterogeneousRootTuple P
    have hbad :
        heterogeneousBadMonochromaticScale P c hfail
          (levels 0) root < levels 1 :=
      heterogeneousBadScale_lt_sparse_succ P c hfail 0 root
    have hNnonempty : ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAt hNdense
    have hNsubFull : N.carrier ⊆ Full.carrier :=
      fun z hz => (hNsub hz).1
    have hNlevel : N.OnLevel L :=
      N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
        (HeterogeneousMatrix.fullLevel_onLevel P L) hNnonempty
    have hNbad : N.DenseAt
        (heterogeneousBadMonochromaticScale P c hfail
          (levels 0) root) :=
      N.denseAt_of_le (Nat.le_of_lt hbad) hNdense
    have hNabove : N.DenseAbove root.1
        (heterogeneousBadMonochromaticScale P c hfail
          (levels 0) root) := by
      intro i z hz _
      exact hNbad i z hz
    have hmono : ∀ z ∈ N.carrier, c z = (0 : Fin 2) := by
      intro z hz
      exact (hNsub hz).2
    exact (heterogeneousBadMonochromaticScale_spec
      P c hfail (levels 0) root)
        ⟨0, N, L, hNlevel, hNabove, hmono⟩

end GeneralTree
end Milliken
