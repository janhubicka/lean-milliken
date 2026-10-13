import Milliken.GeneralTree.HeterogeneousRemark38
import Milliken.GeneralTree.HeterogeneousHDHLBase

/-!
# Exact selected-level reduction for heterogeneous HDHL

Todorčević Remark 3.8 is a level-compression argument. It proves
that a highly dense colour class admits an increasing source-index
sequence such that its complement has no matrix somewhere dense
*between selected source levels*. This is not the same as absence
of an ordinary somewhere-dense matrix in a strong refinement:
source-level compression retains all nodes of each chosen level,
whereas a strong refinement keeps one representative per ambient
child cone.

We isolate the exact missing theorem as a restricted reduced
dichotomy, expressed in the original heterogeneous matrix language.
Once that theorem holds at the sequence supplied by Remark 3.8,
the original highly-dense HDHL statement follows without any
additional combinatorial assumption.

The conversion in this file is proved unconditionally for arbitrary
locally finitely branching coordinate strong trees. The remaining
task is to prove the restricted dichotomy using an actual compressed
tree (or a source-faithful direct adaptation of the reduced induction).
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The reduced dichotomy measured only at a prescribed subsequence
of the actual selected source indices of each coordinate tree. -/
def HeterogeneousRestrictedReducedDichotomy
    (P : Fin d → StrongSubtree U)
    (levels : ℕ → ℕ) : Prop :=
  ∀ Q : Set (Fin d → U),
    (¬ HeterogeneousContainsRestrictedSomewhereDense P levels Qᶜ) →
    ∃ M : HeterogeneousMatrix P,
      M.DenseAt (levels 1) ∧ M.carrier ⊆ Q

/-- Exactly the heterogeneous form of Todorčević's Remark 3.8:
the restricted reduced dichotomy for the selected sequence attached
to each highly dense set implies ordinary HDHL in that dimension.

In particular the only unproved ingredient is the restricted
dichotomy, not an extra version of the Halpern--Läuchli theorem
silently assumed in the use of the compression. -/
theorem heterogeneousHDHL_of_restrictedReduced
    (P : Fin d → StrongSubtree U)
    (hred :
      ∀ (Q : Set (Fin d → U))
        (hQ : HeterogeneousHighlyDense P Q)
        (k : ℕ),
        HeterogeneousRestrictedReducedDichotomy
          P (heterogeneousRemark38Levels P hQ k)) :
    HasHeterogeneousHDHL P := by
  intro Q hQ k hk
  have hno :
      ¬ HeterogeneousContainsRestrictedSomewhereDense
        P (heterogeneousRemark38Levels P hQ k) Qᶜ :=
    heterogeneous_no_restricted_compl_of_highlyDense P Q hQ k
  obtain ⟨M, hM, hSub⟩ := hred Q hQ k Q hno
  have hk1 : k ≤ heterogeneousRemark38Levels P hQ k 1 := by
    exact heterogeneousRemark38Levels_target_le_succ P hQ k 0
  exact ⟨M, M.denseAt_of_le hk1 hM, hSub⟩

end GeneralTree
end Milliken
