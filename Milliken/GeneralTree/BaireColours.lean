import Milliken.GeneralTree.HeterogeneousUniversalMilliken
import Milliken.FiniteColourRamseySpace

/-!
# Finite Baire-measurable colourings of infinite strong subtrees

Todorčević Corollary 6.4 states this for finite Souslin-measurable
colourings. The topological theorem yields the more abstract
Baire-measurable-colour-fibre version, because a topological Ramsey
space homogenizes every Baire-measurable subset of its points.

The implication that Souslin-measurable fibres are Baire-measurable
is an external topological regularity fact (Nikodym); it is not
silently assumed or formalised by this module. This result is the
exact finite-colour Baire consequence of Theorem 6.2.
-/

namespace Milliken
namespace GeneralTree

/-- Every finite colouring of infinite strong subtrees whose colour
fibres have the Baire property in the Ellentuck topology is constant
on all strong subtrees of some infinite strong tree.

This is a separate and more general-dimensional endpoint than fixed
height approximation colouring; the colour depends on an *entire*
infinite strong subtree. -/
theorem millikenFiniteBaireColouring
    (U : AmbientTree)
    {κ : Type*} [Fintype κ]
    (colour : StrongSubtree U → κ)
    (hBaire : ∀ c : κ,
      @BaireMeasurableSet (StrongSubtree U)
        (generalApproximationSystem U).ellentuckTopology
        {T | colour T = c}) :
    ∃ T : StrongSubtree U, ∃ c : κ,
      ∀ S : StrongSubtree U, S.Refines T → colour S = c := by
  let R := generalApproximationSystem U
  let I : StrongSubtree U := identityStrongSubtree U
  have hne : (R.neighborhood (r 0 I) I).Nonempty :=
    ⟨I, StrongSubtree.refines_refl I, rfl⟩
  obtain ⟨T, hTI, c, hmono⟩ :=
    RamseySpace.finiteBaireColouring
      (generalMilliken_unconditional U) (r 0 I) I hne
      colour hBaire
  refine ⟨T, c, ?_⟩
  intro S hST
  exact hmono S ⟨hST, r_zero_eq S I⟩

end GeneralTree
end Milliken
