import Milliken.AmalgamationRefine
import Milliken.PigeonholeLift
import Milliken.Closed
import RamseySpace.AbstractEllentuck

/-!
# The strong-tree Ramsey space and Milliken's theorem

This file assembles the Chapter 6 argument once the strong-subtree
Halpern--Läuchli theorem is available.

A.1 is the approximation system, A.2 the carrier finitization, A.3 is the
finite-stem extension plus depth-boundary splice, A.4 is Lemma 6.1 lifted
through A.3(2), and closedness was proved directly from coherent
approximation codes.  Todorčević's Abstract Ellentuck Theorem then makes the
space of infinite strong subtrees a topological Ramsey space.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

/-- A.1--A.4 for homogeneous strong subtrees, conditional only on the
strong-subtree Halpern--Läuchli theorem. -/
def abstractRamseySpace_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι) :
    RamseySpace.AbstractRamseySpace (TreeSystem ι) :=
  RamseySpace.AbstractRamseySpace.ofStandardAxioms
    (StrongTreeSpace.finitization (ι := ι))
    StrongTreeSpace.amalgamation_nonempty
    StrongTreeSpace.amalgamation_refine_standard
    (pigeonhole_of_strongSubtreeHL_and_refine
      hHL StrongTreeSpace.amalgamation_refine_standard)

/-- Conditional Milliken theorem in the source-facing topological Ramsey
space form. -/
theorem milliken_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι) :
    RamseySpace.IsTopologicalRamseySpace
      (abstractRamseySpace_of_strongSubtreeHL hHL) :=
  RamseySpace.abstractEllentuck
    (abstractRamseySpace_of_strongSubtreeHL hHL)
    StrongTreeSpace.isMetricallyClosed

/-- Equivalent source-facing formulation on all basic neighborhoods. -/
theorem milliken_onBasicNeighborhoods_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι) :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := TreeSystem ι) :=
  RamseySpace.abstractEllentuck_onBasicNeighborhoods
    (abstractRamseySpace_of_strongSubtreeHL hHL)
    StrongTreeSpace.isMetricallyClosed

end Chapter6
end Milliken
