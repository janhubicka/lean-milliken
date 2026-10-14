import Milliken

/-!
# Standalone mathematical API smoke tests

This file is intentionally independent of any downstream application.
It checks that the public umbrella exposes the advertised typed
theorems about locally finitely branching rooted trees, finite
approximations, protected stems and general topological Ramsey
spaces. These are propositions used by a mathematician importing
`Milliken`, not merely references in documentation.
-/

open Milliken
open Milliken.GeneralTree

example (U : AmbientTree) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := generalApproximationSystem U) :=
  generalMilliken_unconditional U

example (U : AmbientTree) :
    HasBoundaryProductHL U :=
  boundaryProductHL_unconditional U

example (U : AmbientTree) :
    HasMillikenFiniteColourProperty U :=
  milliken1979_general_unconditional U

example {U : AmbientTree} {k : ℕ}
    (a : SFinite U k)
    (B T : StrongSubtree U) (n : ℕ)
    (hnk : n ≤ k)
    (hcontained : a.carrier ⊆ B.carrier)
    (hTa : r k T = a)
    (hStem : r n T = r n B) :
    ∃ X : StrongSubtree U,
      X.Refines B ∧ r k X = a ∧ r n X = r n B :=
  exists_refinement_realising_with_stem
    a B T n hnk hcontained hTa hStem

#check RamseySpace.finiteApproximationColouring
#check RamseySpace.finiteBaireColouring
#check RamseySpace.ApproximationSystem.isOpen_approxColourFibre
#check millikenFixedStemFiniteColouring_general
#check millikenFixedStemMonochromatic_general
#check millikenFiniteBaireColouring
#check galvinAlternative_realized
#check IntrinsicFiniteApprox
#check IntrinsicFiniteWitness
