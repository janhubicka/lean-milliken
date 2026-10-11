import Milliken.GeneralTree.PublishedAmalgamation
import RamseySpace.Axioms

/-!
# The general-tree Ramsey-space interface reduces to A.4

The structural A.1 approximation system, published A.2
finitization (6.3), and both halves of Todorčević A.3 have
been formalized for every arbitrary pruned locally finitely
branching rooted ambient tree U.

The remaining combinatorial A.4 is an explicit theorem
*parameter*, not an axiom or an instance. From any proof
of that one-step pigeonhole theorem, this module constructs
the exact verified abstract Ramsey-space structure used by
the existing Abstract Ellentuck library.

Topological closedness is an additional separate obligation
before the unrestricted topological Milliken theorem follows.
-/

namespace Milliken
namespace GeneralTree

/-- The **unproved target property** A.4 for an arbitrary
pruned finitely branching tree U. Its quantifiers are exactly
those of the checked abstract Ramsey-space interface. -/
def HasGeneralPigeonhole (U : AmbientTree) : Prop :=
  ∀ {n : ℕ}
      (a : (generalApproximationSystem U).Approx n)
      (B : (generalApproximationSystem U).Point)
      {d : ℕ},
    (generalBookFinitization U).HasDepth a B d →
      ∀ O : Set ((generalApproximationSystem U).Approx (n + 1)),
        ∃ A : (generalApproximationSystem U).Point,
          A ∈ (generalApproximationSystem U).levelNeighborhood d B ∧
            ((generalApproximationSystem U).oneStepApproximations a A ⊆ O ∨
              Disjoint
                ((generalApproximationSystem U).oneStepApproximations a A)
                O)

/-- Construct the entire A.1–A.4 abstract Ramsey-space structure
from **one explicit hypothesis** proving general-tree A.4.

This is a conditional theorem, *not* a proof of A.4 or Milliken. -/
def abstractRamseySpace_of_pigeonhole
    (U : AmbientTree) (hA4 : HasGeneralPigeonhole U) :
    RamseySpace.AbstractRamseySpace (generalApproximationSystem U) where
  fin := generalBookFinitization U
  amalgamation_nonempty := by
    intro n a B d hd A hA
    exact generalAmalgamation_nonempty a B hd hA
  amalgamation_refine := by
    intro n a B d hd A hAB hne
    exact generalAmalgamation_refine a B hd hAB hne
  pigeonhole := by
    intro n a B d hd O
    exact hA4 a B hd O

end GeneralTree
end Milliken
