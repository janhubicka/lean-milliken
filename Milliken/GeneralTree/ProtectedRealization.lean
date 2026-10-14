import Milliken.GeneralTree.Original1979Conditional
import Milliken.GeneralTree.Coherence

/-!
# Extending finite strong-tree stems within an infinite strong subtree

A realised height-`k` approximation contained in an infinite strong tree
extends to an infinite refinement of that tree. If the finite picture
agrees with a prescribed source-level prefix of height `n ≤ k`, the
refinement can be chosen to preserve that prefix exactly.

This is purely geometric: it does not assume a colouring, a Ramsey
theorem, or a uniform bound on the ambient branching degree. It is a
useful companion to fixed-stem applications of Milliken's theorem.

The finite object here is the library's `FiniteApprox`, with an
infinite-realisation witness. An intrinsic finite version requires the
separately tracked intrinsic-to-realised extension equivalence.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Relative finite-approximation realisation with a protected prefix.

Suppose `a` is the height-`k` restriction of some strong tree `T`,
its carrier lies in the strong tree `B`, and `T` and `B` agree on their
first `n` selected source levels. Then `a` is realised by a strong
refinement of `B` which preserves precisely the same first `n` levels.

In particular, there is no additional prefix-completion hypothesis
beyond `n ≤ k` and the stated carrier containment. -/
theorem exists_refinement_realising_with_stem
    (a : SFinite U k)
    (B T : StrongSubtree U)
    (n : ℕ) (hnk : n ≤ k)
    (hcontained : a.carrier ⊆ B.carrier)
    (hTa : r k T = a)
    (hStem : r n T = r n B) :
    ∃ X : StrongSubtree U,
      X.Refines B ∧ r k X = a ∧ r n X = r n B := by
  obtain ⟨X, hXB, hXa⟩ :=
    exists_refinement_realising_general a B hcontained
  have hXT : r k X = r k T := hXa.trans hTa.symm
  have hprefix : r n X = r n T :=
    r_coherent_le X T k hXT n hnk
  exact ⟨X, hXB, hXa, hprefix.trans hStem⟩

end GeneralTree
end Milliken
