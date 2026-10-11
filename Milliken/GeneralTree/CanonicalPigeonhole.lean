import Milliken.GeneralTree.PigeonholeInterface
import RamseySpace.Axioms

/-!
# From canonical strong-tree pigeonhole to published A.4

Todorčević's Lemma 6.1 is the Halpern–Läuchli step: at a canonical
stem r_n(T), color the finite product of successor cones, find common
strong subtrees with one level sequence, and graft them to T's stem.

The passage from this canonical-stem conclusion to the full A.4
quantification over a finite stem a at an arbitrary published depth
d in B is purely formal. It uses the verified A.3(1) to realize
a, and A.3(2) to protect the depth-d prefix during the final lift.

This file formalizes precisely that lifting for arbitrary locally
finitely branching pruned ambient trees. No heterogeneous-cone
Halpern–Läuchli theorem is assumed or proved here.
-/

namespace Milliken
namespace GeneralTree

/-- The canonical-stem pigeonhole property: for any coloring of
height-(n+1) approximations, a strong refinement preserving the
first n source levels makes all its one-step extensions monochromatic.

For arbitrary ambient trees this is an unproved target of the
boundary-product Halpern–Läuchli argument, not an axiom. -/
def HasCanonicalPigeonhole (U : AmbientTree) : Prop :=
  ∀ (n : ℕ) (T : SInfinity U)
      (O : Set (SFinite U (n + 1))),
    ∃ R : SInfinity U,
      R ∈ (generalApproximationSystem U).levelNeighborhood n T ∧
        ((generalApproximationSystem U).oneStepApproximations
              (r n T) R ⊆ O ∨
          Disjoint
            ((generalApproximationSystem U).oneStepApproximations
              (r n T) R) O)

/-- Published A.4 follows formally from canonical Lemma 6.1 and
the verified A.3 amalgamation laws. This is an implication,
not a proof of canonical pigeonhole or HL. -/
theorem generalPigeonhole_of_canonical
    (U : AmbientTree)
    (hCanonical : HasCanonicalPigeonhole U) :
    HasGeneralPigeonhole U := by
  intro n a B d hd O
  let S := generalApproximationSystem U
  have hB : B ∈ S.levelNeighborhood d B :=
    S.self_mem_levelNeighborhood d B
  obtain ⟨T, hTB⟩ :=
    generalAmalgamation_nonempty a B hd hB
  obtain ⟨R, hRT, hRh⟩ := hCanonical n T O
  have hRT' : R.Refines T := hRT.1
  have hRnT : r n R = r n T := hRT.2
  have hTBa : r n T = a := hTB.2
  have hRB : R.Refines B := hRT'.trans hTB.1
  have hRa : r n R = a := hRnT.trans hTBa
  have hne : (S.neighborhood a R).Nonempty :=
    ⟨R, StrongSubtree.refines_refl R, hRa⟩
  obtain ⟨A, hAB, hsub⟩ :=
    generalAmalgamation_refine a B hd hRB hne
  have hone :
      S.oneStepApproximations a A ⊆
      S.oneStepApproximations a R := by
    rintro b ⟨X, hXA, hXb⟩
    exact ⟨X, hsub hXA, hXb⟩
  have hRh' :
      S.oneStepApproximations a R ⊆ O ∨
        Disjoint (S.oneStepApproximations a R) O := by
    simpa only [hTBa] using hRh
  refine ⟨A, hAB, ?_⟩
  rcases hRh' with hpos | hneg
  · exact Or.inl (hone.trans hpos)
  · right
    apply Set.disjoint_left.mpr
    intro b hb hO
    exact (Set.disjoint_left.mp hneg) (hone hb) hO

end GeneralTree
end Milliken
