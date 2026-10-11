import Milliken.GeneralTree.BoundaryCones

/-!
# Precise general Halpern–Läuchli product interface for A.4

The checked homogeneous theorem
  HalpernLauchli.HalesJewettBridge.strongSubtreeHL
acts on products of copies of the full homogeneous List ι tree,
and the verified FiniteIndexedHL module allows any finite index type.

The *published arbitrary-tree* application instead needs the same
level-product conclusion for a finite family of possibly
non-isomorphic strong subtrees of one arbitrary pruned locally
finitely branching ambient tree U, whose starting selected levels
are synchronized.

We state this exact general product theorem as a **Prop target**,
not an axiom or a proved theorem. The checked theorem below
merely specializes its finite family to the actual finite family
of source-boundary successor cones. Once this general version of
HL is established, the only remaining steps to A.4 are canonical
boundary tuple grafting and the already verified A.3 lift.
-/

namespace Milliken
namespace GeneralTree

/-- The standard finite-dimensional strong-tree Halpern–Läuchli
statement for arbitrary strong factors inside U, in a form with a
single common ambient selected-level map.

Unlike the existing *proved* homogeneous-List HL, this general
property is not yet proved in Lean. It is a target definition,
not an axiom or an imported theorem. -/
def HasGeneralProductHL (U : AmbientTree) : Prop :=
  ∀ (d colors : ℕ) [NeZero colors]
      (P : Fin d → StrongSubtree U)
      (L : ℕ → ℕ)
      (_hP : ∀ i, (P i).levels = L)
      (colour : (Fin d → U) → Fin colors),
    ∃ c : Fin colors,
      ∃ M : ℕ → ℕ,
        ∃ F : Fin d → StrongSubtree U,
          StrictMono M ∧
            (∀ i, (F i).Refines (P i) ∧ (F i).levels = M) ∧
            ∀ (k : ℕ) (x : Fin d → U),
              (∀ i, x i ∈ (F i).sourceLevel k) →
                colour x = c

/-- The exact heterogeneous source-boundary product HL required in
the canonical one-step pigeonhole argument. Its index set is finite
but may have arbitrarily large cardinality depending on the stem. -/
def HasBoundaryProductHL (U : AmbientTree) : Prop :=
  ∀ (T : StrongSubtree U) (n colors : ℕ) [NeZero colors]
      (colour : (SourceBoundary T n → U) → Fin colors),
    ∃ c : Fin colors,
      ∃ M : ℕ → ℕ,
        ∃ F : SourceBoundary T n → StrongSubtree U,
          StrictMono M ∧
            (∀ i, (F i).Refines (boundaryCones T n i) ∧
              (F i).levels = M) ∧
            ∀ (k : ℕ) (x : SourceBoundary T n → U),
              (∀ i, x i ∈ (F i).sourceLevel k) →
                colour x = c

/-- Reindex generalized product HL to the *actual source
boundary cones* of a finite strong stem. This is the same
finite-index equivalence used by the proved homogeneous HL.

No HL proof is hidden in this conversion: the general product
theorem remains the explicit input. -/
theorem boundaryProductHL_of_generalProductHL
    (U : AmbientTree)
    (hHL : HasGeneralProductHL U) :
    HasBoundaryProductHL U := by
  classical
  intro T n colors hcolors colour
  let d : ℕ := Fintype.card (SourceBoundary T n)
  let e : Fin d ≃ SourceBoundary T n :=
    (Fintype.equivFin (SourceBoundary T n)).symm
  let P : Fin d → StrongSubtree U :=
    fun i => boundaryCones T n (e i)
  let L : ℕ → ℕ := fun k => T.levels (n + k)
  have hPL : ∀ i, (P i).levels = L := by
    intro i
    exact boundaryCones_levels T n (e i)
  let colour' : (Fin d → U) → Fin colors :=
    fun x => colour (fun i => x (e.symm i))
  obtain ⟨c, M, F, hM, hF, hhom⟩ :=
    hHL d colors P L hPL colour'
  let G : SourceBoundary T n → StrongSubtree U :=
    fun i => F (e.symm i)
  refine ⟨c, M, G, hM, ?_, ?_⟩
  · intro i
    obtain ⟨hinc, hlev⟩ := hF (e.symm i)
    constructor
    · change (F (e.symm i)).Refines (boundaryCones T n i)
      simpa only [P, e.apply_symm_apply] using hinc
    · exact hlev
  · intro k x hx
    have hy : ∀ i : Fin d,
        x (e i) ∈ (F i).sourceLevel k := by
      intro i
      simpa only [G, e.symm_apply_apply] using hx (e i)
    have hcol := hhom k (fun i => x (e i)) hy
    change colour (fun j => x (e (e.symm j))) = c at hcol
    simpa only [e.apply_symm_apply] using hcol

end GeneralTree
end Milliken
