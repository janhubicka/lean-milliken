import Milliken.GeneralTree.HeterogeneousFiniteWitness

/-!
# Sparse finite Halpern--Läuchli witnesses for heterogeneous trees

This is the compactness step of Todorčević's §3.2 proof on genuine
arbitrary pruned locally finitely branching strong-tree factors.

Assuming HDHL in the same dimension, every binary colouring has a
finite monochromatic matrix witnessing either global density in
colour zero or somewhere density between consecutive *prescribed*
selected source indices in colour one. Compactness then reduces
all these finite certificates to finitely many witnesses.

The dependence on source indices is important: the ambient levels
may differ across coordinates and the degrees may grow unboundedly.
This file does not assume a fixed branching alphabet or an
unproved A4/strong-tree HL axiom.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A sparse cone-density witness between consecutive entries of a
specified strictly increasing sequence of source indices. -/
def HeterogeneousSparseSomewhereDense
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ)
    (M : HeterogeneousMatrix P) : Prop :=
  ∃ q : ℕ, ∃ base : HeterogeneousLevelTuple P (levels q),
    M.DenseAbove base.1 (levels (q + 1))

/-- A finite monochromatic certificate for a binary product
colouring of heterogeneous strong-tree factors. -/
structure HeterogeneousSparseFiniteHLWitness
    (P : Fin d → StrongSubtree U)
    (k : ℕ) (levels : ℕ → ℕ) where
  M : HeterogeneousMatrix P
  color : Fin 2
  coordFinite : ∀ i, (M.coord i).Finite
  shape :
    (color = 0 ∧ M.DenseAt k) ∨
      (color = 1 ∧ HeterogeneousSparseSomewhereDense P levels M)

namespace HeterogeneousSparseFiniteHLWitness

variable {P : Fin d → StrongSubtree U}
variable {k : ℕ} {levels : ℕ → ℕ}

theorem carrierFinite
    (W : HeterogeneousSparseFiniteHLWitness P k levels) :
    W.M.carrier.Finite :=
  W.M.carrier_finite W.coordFinite

/-- Cylinder of colourings homogeneous on the finite witness. -/
def cylinder
    (W : HeterogeneousSparseFiniteHLWitness P k levels) :
    Set ((Fin d → U) → Fin 2) :=
  {c | ∀ x ∈ W.M.carrier, c x = W.color}

theorem cylinder_isOpen
    (W : HeterogeneousSparseFiniteHLWitness P k levels) :
    IsOpen W.cylinder := by
  have heq :
      W.cylinder =
        ⋂ x ∈ W.M.carrier,
          {c : (Fin d → U) → Fin 2 | c x = W.color} := by
    ext c
    simp [cylinder]
  rw [heq]
  apply W.carrierFinite.isOpen_biInter
  intro x hx
  change IsOpen
    ((fun c : (Fin d → U) → Fin 2 => c x) ⁻¹' {W.color})
  exact (isOpen_discrete _).preimage (continuous_apply x)

end HeterogeneousSparseFiniteHLWitness

/-- HDHL produces a finite monochromatic certificate for every
binary colouring, at any prescribed cofinal sequence of source indices.
The colour-one alternative is a cone matrix at two adjacent selected
indices; its base need not be the root or a common ambient level. -/
theorem exists_heterogeneousSparseFiniteHLWitness_of_hdhl
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    {k : ℕ} (hk : 0 < k)
    {levels : ℕ → ℕ}
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q)
    (c : (Fin d → U) → Fin 2) :
    ∃ W : HeterogeneousSparseFiniteHLWitness P k levels,
      c ∈ W.cylinder := by
  classical
  let K0 : Set (Fin d → U) := {x | c x = 0}
  rcases heterogeneousAsymmetric_of_hdhl P hHDHL K0 with hzero | hone
  · obtain ⟨M, hMdense, hMsub⟩ := hzero k hk
    let N : HeterogeneousMatrix P := M.finiteDenseCore hMdense
    let W : HeterogeneousSparseFiniteHLWitness P k levels := {
      M := N
      color := 0
      coordFinite := M.finiteDenseCore_coord_finite hMdense
      shape := Or.inl ⟨rfl, M.finiteDenseCore_denseAt hMdense⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier :=
      M.finiteDenseCore_subset hMdense hx
    exact hMsub hxM
  · obtain ⟨base, hbase, hall⟩ := hone
    let rank : Fin d → ℕ :=
      fun i => Classical.choose
        ((P i).carrier_levels (base i) (hbase i))
    have hrank (i : Fin d) :
        base i ∈ (P i).sourceLevel (rank i) :=
      ⟨hbase i, Classical.choose_spec
        ((P i).carrier_levels (base i) (hbase i))⟩
    let r : ℕ := Finset.univ.sup rank
    have hrank_le (i : Fin d) : rank i ≤ r :=
      Finset.le_sup (f := rank) (Finset.mem_univ i)
    obtain ⟨q, hrq⟩ := hunbounded r
    have hraise (i : Fin d) :
        ∃ z : U, z ∈ (P i).sourceLevel (levels q) ∧
          base i ≤ z :=
      (P i).exists_sourceLevel_descendant
        ((hrank_le i).trans hrq) (hrank i)
    let raised : Fin d → U :=
      fun i => Classical.choose (hraise i)
    have hra (i : Fin d) :
        raised i ∈ (P i).sourceLevel (levels q) ∧
          base i ≤ raised i :=
      Classical.choose_spec (hraise i)
    let raisedTuple : HeterogeneousLevelTuple P (levels q) :=
      ⟨raised, fun i => (hra i).1⟩
    obtain ⟨M, hMdense, hMsub⟩ := hall (levels (q + 1))
    let R : HeterogeneousMatrix P := M.restrictAbove raised
    have hRdense : R.DenseAbove raised (levels (q + 1)) := by
      intro i x hx hrx
      obtain ⟨y, hy, hxy⟩ :=
        hMdense i x hx ((hra i).2.trans hrx)
      exact ⟨y, ⟨hy, hrx.trans hxy⟩, hxy⟩
    let N : HeterogeneousMatrix P :=
      R.finiteDenseAboveCore raised hRdense
    let W : HeterogeneousSparseFiniteHLWitness P k levels := {
      M := N
      color := 1
      coordFinite := R.finiteDenseAboveCore_coord_finite raised hRdense
      shape := Or.inr ⟨rfl, q, raisedTuple,
        R.finiteDenseAboveCore_denseAbove raised hRdense⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxR : x ∈ R.carrier :=
      R.finiteDenseAboveCore_subset raised hRdense hx
    have hxM : x ∈ M.carrier :=
      M.restrictAbove_carrier_subset raised hxR
    have hxCompl : x ∈ K0ᶜ := hMsub hxM
    have hne : c x ≠ (0 : Fin 2) := by
      intro h0
      exact hxCompl h0
    exact Fin.eq_one_of_ne_zero (c x) hne

/-- The open cylinders of finite monochromatic witnesses cover the
entire compact product space of binary colourings. -/
theorem heterogeneousSparseFiniteHLWitness_cover
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    {k : ℕ} (hk : 0 < k)
    {levels : ℕ → ℕ}
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    (Set.univ : Set ((Fin d → U) → Fin 2)) ⊆
      ⋃ W : HeterogeneousSparseFiniteHLWitness P k levels,
        W.cylinder := by
  intro c hc
  obtain ⟨W, hW⟩ :=
    exists_heterogeneousSparseFiniteHLWitness_of_hdhl
      P hHDHL hk hlevels hunbounded c
  exact Set.mem_iUnion.2 ⟨W, hW⟩

/-- Finite subcover of the binary colouring space by finite
heterogeneous density witnesses. This is the combinatorial
compactness core of the sparse finite HL statement. -/
theorem exists_heterogeneousSparseFiniteHLWitness_subcover
    (P : Fin d → StrongSubtree U)
    (hHDHL : HasHeterogeneousHDHL P)
    {k : ℕ} (hk : 0 < k)
    {levels : ℕ → ℕ}
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    ∃ F : Finset (HeterogeneousSparseFiniteHLWitness P k levels),
      (Set.univ : Set ((Fin d → U) → Fin 2)) ⊆
        ⋃ W ∈ F, W.cylinder := by
  classical
  exact isCompact_univ.elim_finite_subcover
    (fun W : HeterogeneousSparseFiniteHLWitness P k levels =>
      W.cylinder)
    (fun W => W.cylinder_isOpen)
    (heterogeneousSparseFiniteHLWitness_cover
      P hHDHL hk hlevels hunbounded)

end GeneralTree
end Milliken
