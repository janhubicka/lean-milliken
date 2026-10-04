import Milliken.HalpernLauchli.FiniteWitness
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Compact

/-!
# Compactness bridge to finite Halpern--Läuchli

Corollary 3.7 gives, for every binary coloring of the full product, either a
color-zero dense matrix or a color-one somewhere-dense matrix.  The witnesses
may be thinned to finite matrices.  Hence each witness determines a clopen
cylinder in the compact product space of binary colorings, and these cylinders
cover the whole coloring space.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

abbrev BinaryColoring (ι : Type u) (d : ℕ) :=
  (Fin d → Node ι) → Fin 2

/-- A finite monochromatic witness of the asymmetric dichotomy at target
scale k. -/
structure FiniteHLWitness (ι : Type u) (d k : ℕ) where
  M : Matrix ι d
  color : Fin 2
  coordFinite : ∀ i, (M.coord i).Finite
  shape :
    (color = 0 ∧ M.DenseAt k) ∨
      (color = 1 ∧ M.SomewhereDense)

namespace FiniteHLWitness

variable {d k : ℕ}

theorem carrierFinite
    (W : FiniteHLWitness ι d k) :
    W.M.carrier.Finite :=
  W.M.carrier_finite W.coordFinite

/-- Colorings which are constant with the witness color on its finite
carrier. -/
def cylinder
    (W : FiniteHLWitness ι d k) :
    Set (BinaryColoring ι d) :=
  {c | ∀ x ∈ W.M.carrier, c x = W.color}

theorem cylinder_isOpen
    (W : FiniteHLWitness ι d k) :
    IsOpen W.cylinder := by
  have heq :
      W.cylinder =
        ⋂ x ∈ W.M.carrier,
          {c : BinaryColoring ι d | c x = W.color} := by
    ext c
    simp [cylinder]
  rw [heq]
  apply W.carrierFinite.isOpen_biInter
  intro x hx
  change IsOpen ((fun c : BinaryColoring ι d => c x) ⁻¹' {W.color})
  exact (isOpen_discrete _).preimage (continuous_apply x)

end FiniteHLWitness

/-- Every binary coloring belongs to a finite witness cylinder, assuming
HDHL in the given dimension. -/
theorem exists_finiteHLWitness_of_hdhl
    [Finite ι] [Nonempty ι]
    {d k : ℕ}
    (hHDHL : HDHL ι d)
    (c : BinaryColoring ι d) :
    ∃ W : FiniteHLWitness ι d k, c ∈ W.cylinder := by
  classical
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  rcases asymmetric_of_hdhl hHDHL K0 with hzero | hone
  · rcases hzero (k + 1) (by omega) with
      ⟨M, hMdense, hMsub⟩
    have hMk : M.DenseAt k :=
      M.denseAt_of_le (Nat.le_succ k) hMdense
    let N : Matrix ι d := M.finiteDenseCore hMk
    let W : FiniteHLWitness ι d k := {
      M := N
      color := 0
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseCore_coord_finite hMk
      shape := Or.inl ⟨rfl, by
        dsimp [N]
        exact M.finiteDenseCore_dense hMk⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier := by
      exact M.finiteDenseCore_subset hMk hx
    exact hMsub hxM
  · rcases hone with ⟨base, ⟨r, hbaseLevel⟩, hall⟩
    let q := r + 1
    rcases hall q with ⟨M, hMdense, hMsub⟩
    let N : Matrix ι d :=
      M.finiteDenseAboveCore base hMdense
    have hbase : ∀ i, (base i).length < q := by
      intro i
      rw [hbaseLevel i]
      dsimp [q]
      omega
    have hNsome : N.SomewhereDense := by
      refine ⟨base, q, hbase, ?_⟩
      dsimp [N]
      exact M.finiteDenseAboveCore_dense base hMdense
    let W : FiniteHLWitness ι d k := {
      M := N
      color := 1
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseAboveCore_coord_finite base hMdense
      shape := Or.inr ⟨rfl, hNsome⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier := by
      exact M.finiteDenseAboveCore_subset base hMdense hx
    have hx1 : x ∈ K0ᶜ := hMsub hxM
    have hne : c x ≠ (0 : Fin 2) := by
      intro h0
      exact hx1 h0
    apply Fin.eq_of_val_eq
    omega

/-- The finite witness cylinders form an open cover of all binary colorings. -/
theorem finiteHLWitness_cover
    [Finite ι] [Nonempty ι]
    {d k : ℕ}
    (hHDHL : HDHL ι d) :
    (Set.univ : Set (BinaryColoring ι d)) ⊆
      ⋃ W : FiniteHLWitness ι d k, W.cylinder := by
  intro c hc
  rcases exists_finiteHLWitness_of_hdhl hHDHL c with ⟨W, hW⟩
  exact Set.mem_iUnion.2 ⟨W, hW⟩

/-- Compactness extracts finitely many witness cylinders which already cover
the full binary-coloring space. -/
theorem exists_finiteHLWitness_subcover
    [Finite ι] [Nonempty ι]
    {d k : ℕ}
    (hHDHL : HDHL ι d) :
    ∃ F : Finset (FiniteHLWitness ι d k),
      (Set.univ : Set (BinaryColoring ι d)) ⊆
        ⋃ W ∈ F, W.cylinder := by
  classical
  exact isCompact_univ.elim_finite_subcover
    (fun W : FiniteHLWitness ι d k => W.cylinder)
    (fun W => W.cylinder_isOpen)
    (finiteHLWitness_cover hHDHL)

end HalpernLauchli
end Milliken
