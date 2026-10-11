import Milliken.Applications.VectorHL

/-!
# Strong-subtree Halpern–Läuchli indexed by any finite type

The verified Hales–Jewett bridge is stated using `Fin d`.
Applications to finite boundaries naturally carry an arbitrary finite
index type instead. This file proves the change of indices once.

The coordinate trees here are homogeneous `List ι`. The theorem
does *not* supply Halpern–Läuchli for arbitrary non-isomorphic
locally finite ambient trees; that is a separate generalization.
-/

namespace Milliken
namespace Applications

universe u v

/-- The coordinatewise strong-subtree level condition for an arbitrary
finite index type. -/
def IndexedHasCommonLevels {ι : Type u} {J : Type v}
    (F : J → StrongEmbedding ι) (levels : ℕ → ℕ) : Prop :=
  StrictMono levels ∧
    ∀ j s, ((F j).toFun s).length = levels s.length

/-- Strong-subtree Halpern–Läuchli with an arbitrary finite family
of homogeneous coordinates and a single common strictly increasing
level sequence, obtained by reindexing the already verified theorem. -/
theorem finiteIndexedStrongSubtreeHL
    {ι : Type u} [Finite ι] [Nonempty ι]
    {J : Type v} [Fintype J]
    (colors : ℕ) [NeZero colors]
    (colour : (J → Node ι) → Fin colors) :
    ∃ c : Fin colors,
      ∃ levels : ℕ → ℕ,
        ∃ F : J → StrongEmbedding ι,
          IndexedHasCommonLevels F levels ∧
            ∀ n : ℕ, ∀ x : J → Node ι,
              (∀ j, (x j).length = n) →
                colour (fun j => (F j).toFun (x j)) = c := by
  classical
  let d := Fintype.card J
  let e : Fin d ≃ J := (Fintype.equivFin J).symm
  let colour' : (Fin d → Node ι) → Fin colors :=
    fun x => colour (fun j => x (e.symm j))
  obtain ⟨c, levels, G, hGL, hhom⟩ :=
    (HalpernLauchli.HalesJewettBridge.strongSubtreeHL ι)
      d colors colour'
  let F : J → StrongEmbedding ι :=
    fun j => G (e.symm j)
  refine ⟨c, levels, F, ⟨hGL.1, ?_⟩, ?_⟩
  · intro j s
    exact hGL.2 (e.symm j) s
  · intro n x hx
    have h := hhom n (fun i => x (e i)) (by
      intro i
      exact hx (e i))
    change colour (fun j => (F j).toFun (x j)) = c
    simpa [colour', F] using h

end Applications
end Milliken
