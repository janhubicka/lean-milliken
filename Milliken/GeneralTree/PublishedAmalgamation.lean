import Milliken.GeneralTree.MixedStrong
import Milliken.GeneralTree.ProtectedIndex
import Milliken.GeneralTree.ThinningApprox
import Milliken.GeneralTree.ProtectedTail
import Milliken.GeneralTree.SpliceAmalgamation
import RamseySpace.Axioms

/-!
# Todorčević A.3(2) for arbitrary locally finitely branching strong trees

Given a finite strong stem a at depth d in B, and a refinement A ≤ B
admitting an extension of a, choose X ∈ [a,A]. The last selected
source level of a is X.sourceLevel n, contained in B.sourceLevel j,
where d=j+1. This identifies the selected ambient ranks at the cut.

Construct the strictly increasing protected level index f of B:
it fixes indices through j and follows X's future ambient levels.
Thin B along f, obtaining D. Its full first j+1 selected levels
equal B's, while from j onward its selected ambient levels equal
those of X from n onward.

Now use the genuine mixed strong-tree constructor: retain D's full
depth prefix, follow X in the used X-frontier cones, and follow D
in unused frontier cones. The resulting C belongs to [d,B] and
its used cones are confined to X. Every further refinement of C
with stem a therefore belongs to X and hence A. This is exactly
the published non-standard A.3(2), with no global degree bound.

The empty stem is handled separately at depth zero.

Together with the checked A.1, A.2 and A.3(1), this completes
A.1--A.3. A.4, closedness and the unrestricted Milliken theorem
are separate outstanding obligations.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Todorčević's published A.3(2): a nonempty a-neighborhood
inside a strong refinement A of B may be protected while
preserving the depth-d prefix of B.

All hypotheses and the conclusion use the actual published
A.1/A.2 interfaces of arbitrary locally finite rooted trees.
No homogeneous alphabet or uniform branching bound occurs. -/
theorem generalAmalgamation_refine
    {m : ℕ} (a : (generalApproximationSystem U).Approx m)
    (B : (generalApproximationSystem U).Point) {d : ℕ}
    (hd : (generalBookFinitization U).HasDepth a B d)
    {A : (generalApproximationSystem U).Point}
    (hAB : (generalApproximationSystem U).le A B)
    (hne : ((generalApproximationSystem U).neighborhood a A).Nonempty) :
    ∃ C : (generalApproximationSystem U).Point,
      C ∈ (generalApproximationSystem U).levelNeighborhood d B ∧
        (generalApproximationSystem U).neighborhood a C ⊆
          (generalApproximationSystem U).neighborhood a A := by
  change A.Refines B at hAB
  change (BasicNeighborhood a A).Nonempty at hne
  change ∃ C : SInfinity U,
    C ∈ BasicNeighborhood (r d B) B ∧
      BasicNeighborhood a C ⊆ BasicNeighborhood a A
  cases m with
  | zero =>
      have hd0 : d = 0 := bookDepth_zero_of_empty a B hd
      subst d
      refine ⟨A, ⟨hAB, r_zero_eq A B⟩, ?_⟩
      exact Set.Subset.rfl
  | succ n =>
      obtain ⟨X, hXA, hXa⟩ := hne
      have hXB : X.Refines B := hXA.trans hAB
      obtain ⟨j, hdEq, hfronta⟩ :=
        bookDepth_succ_lastLevel a B hd
      have hMaxX : X.sourceLevel n = maxLevel a := by
        calc
          X.sourceLevel n = maxLevel (r (n + 1) X) :=
            (maxLevel_r_succ X n).symm
          _ = maxLevel a := by rw [hXa]
      have hfrontB : X.sourceLevel n ⊆ B.sourceLevel j := by
        rw [hMaxX]
        exact hfronta
      have hmatch : X.levels n = B.levels j :=
        B.frontier_levels_eq_of_subset X j n hfrontB

      let f : ℕ → ℕ := X.protectedIndex B hXB n j
      have hf : StrictMono f :=
        X.protectedIndex_strictMono B hXB n j hmatch
      have hf0 : f 0 = 0 :=
        X.protectedIndex_zero B hXB n j hmatch
      have hfixed : ∀ k : ℕ, k ≤ j → f k = k := by
        intro k hk
        exact X.protectedIndex_initial B hXB n j hmatch hk

      let D : SInfinity U := B.thinStrong f hf hf0
      have hDB : D.Refines B := B.thinStrong_refines f hf hf0
      have hDprefix : r (j + 1) D = r (j + 1) B :=
        B.thinStrong_approx_succ_of_fixed f hf hf0 j hfixed
      have hDtop : D.sourceLevel j = B.sourceLevel j :=
        B.thinStrong_sourceLevel_of_fixed f hf hf0 j
          hfixed (le_refl j)
      have hfrontD : X.sourceLevel n ⊆ D.sourceLevel j := by
        rw [hDtop]
        exact hfrontB
      have hlevels : ∀ t : ℕ,
          D.levels (j + t) = X.levels (n + t) := by
        intro t
        change B.levels (f (j + t)) = X.levels (n + t)
        exact X.protectedIndex_levels_at_tail B hXB n j t

      let C : SInfinity U := D.mixedStrong X j n hfrontD hlevels
      have hCB : C.Refines B :=
        StrongSubtree.mixedStrong_refines_common
          B D X j n hfrontD hlevels hDB hXB
      have hCM : r (j + 1) C = r (j + 1) B := by
        calc
          r (j + 1) C = r (j + 1) D :=
            D.mixedStrong_approx_succ X j n hfrontD hlevels
          _ = r (j + 1) B := hDprefix
      have hCd : r d C = r d B := by
        rw [hdEq]
        exact hCM
      have hCtail : ∀ z ∈ C.carrier,
          (∃ x ∈ X.sourceLevel n, x ≤ z) →
            z ∈ X.carrier := by
        intro z hz hcone
        change z ∈ U.upwardCones (X.sourceLevel n) at hcone
        exact D.mixedStrong_used_sector_in_X
          X j n hfrontD hlevels hz hcone
      have hsub :
          BasicNeighborhood (r (n + 1) X) C ⊆
            BasicNeighborhood (r (n + 1) X) X :=
        basicNeighborhood_subset_of_protected_tail X C n hCtail
      rw [hXa] at hsub
      exact ⟨C, ⟨hCB, hCd⟩,
        hsub.trans (basicNeighborhood_mono a hXA)⟩

end GeneralTree
end Milliken
