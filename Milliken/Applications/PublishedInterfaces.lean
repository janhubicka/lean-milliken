import Milliken.Applications.FiniteColour
import Milliken.Applications.FixedPrefix

/-!
# Published interfaces for the verified homogeneous case

**Scope:** the ambient is the full tree `List ι` for a fixed finite,
nonempty alphabet. Todorčević Theorem 6.2 quantifies over **all** rooted,
finitely branching, pruned trees, including trees of unbounded finite
branching. Therefore the present API must *not* be advertised as a complete
formalisation of the general ambient theorem.

Reference: S. Todorčević, *Introduction to Ramsey Spaces* (2010), Chapter 6,
Theorem 6.2 and Corollary 6.5.
Reference: K. R. Milliken, *A Ramsey theorem for trees*,
J. Combin. Theory Ser. A 26 (1979), 215–237.
-/

namespace Milliken
namespace Applications

universe u

/-- Todorčević, Theorem 6.2, on a homogeneous ambient tree. -/
theorem todorcevic62_homogeneous
    {ι : Type u} [Finite ι] [Nonempty ι] :
    RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
      (S := Chapter6.TreeSystem ι) :=
  Chapter6.milliken_onBasicNeighborhoods (ι := ι)

end Applications
end Milliken
