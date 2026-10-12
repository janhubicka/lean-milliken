import Milliken.GeneralTree.HeterogeneousAllConeStabilization

/-!
# Simultaneous uniform stabilization for finitely many product sets

One uniform finite-boundary stabilization handles one product set.
Here we iterate over any finite collection of product sets, while
preserving previously established uniform cone constancy.

The preservation proof uses the exact finite frontier equivalence:
every node of the refined source-n boundary is above a unique
old source-n node, and the prior cone-constancy transfers to it
using the common synchronized source-index map.

The result is the finite-family theorem required to stabilize
simultaneously all last-coordinate sections indexed by the finite
source-t last-coordinate level in Todorčević's induction.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Every new source-n boundary tuple has an old source-n
ancestor under a coordinatewise protected strong refinement. -/
theorem exists_oldBoundaryTuple_of_protected
    (P R : Fin d → StrongSubtree U)
    (n : ℕ)
    (hRP : ∀ i, (R i).Refines (P i))
    (hprefix : ∀ i, r n (R i) = r n (P i))
    (b : HeterogeneousLevelTuple R n) :
    ∃ old : HeterogeneousLevelTuple P n,
      ∀ i, old.1 i ≤ b.1 i := by
  classical
  let e (i : Fin d) :
      SourceBoundary (P i) n ≃ SourceBoundary (R i) n :=
    (P i).protectedBoundaryEquiv
      (R i) (hRP i) (hprefix i)
  let oldSrc (i : Fin d) : SourceBoundary (P i) n :=
    (e i).symm ⟨b.1 i, b.2 i⟩
  let old : HeterogeneousLevelTuple P n :=
    ⟨fun i => (oldSrc i).1, fun i => (oldSrc i).2⟩
  refine ⟨old, ?_⟩
  intro i
  have hLift :
      (oldSrc i).1 ≤
        ((P i).protectedBoundaryLift
          (R i) (hRP i) (hprefix i) (oldSrc i)).1 :=
    (P i).protectedBoundaryLift_above
      (R i) (hRP i) (hprefix i) (oldSrc i)
  have hEq :
      (P i).protectedBoundaryLift
        (R i) (hRP i) (hprefix i) (oldSrc i) =
      (⟨b.1 i, b.2 i⟩ : SourceBoundary (R i) n) := by
    change (e i) ((e i).symm ⟨b.1 i, b.2 i⟩) =
      ⟨b.1 i, b.2 i⟩
    exact (e i).apply_symm_apply _
  rw [hEq] at hLift
  exact hLift

/-- Uniform cone constancy at every source-n boundary point is
hereditary under further synchronized protected strong refinements. -/
theorem HeterogeneousUniformConeConstant.refinement
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hR : ∀ i, (R i).levels = M)
    (hRP : ∀ i, (R i).Refines (P i))
    (n : ℕ)
    (hprefix : ∀ i, r n (R i) = r n (P i))
    (A : Set (Fin d → U))
    (hconst : HeterogeneousUniformConeConstant P A n) :
    HeterogeneousUniformConeConstant R A n := by
  intro b
  obtain ⟨old, hold⟩ :=
    exists_oldBoundaryTuple_of_protected P R n hRP hprefix b
  exact HeterogeneousConeConstant.refinement
    P R hd L M hP hR hRP
    A old (hconst old) b hold

/-- One synchronized strong refinement simultaneously makes
every cone at source level n constant for *each* product set
in an arbitrary finite collection. It preserves r_n. -/
theorem exists_heterogeneousUniformConeStabilization_finset
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (n : ℕ) (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (sets : Finset (Set (Fin d → U))) :
    ∃ (M : ℕ → ℕ) (R : Fin d → StrongSubtree U),
      StrictMono M ∧
      (∀ i, (R i).Refines (P i) ∧
        r n (R i) = r n (P i) ∧
        (R i).levels = M) ∧
      (∀ A ∈ sets, HeterogeneousUniformConeConstant R A n) := by
  classical
  induction sets using Finset.induction_on with
  | empty =>
      let i0 : Fin d := ⟨0, hd⟩
      have hL : StrictMono L := by
        rw [← hP i0]
        exact (P i0).levels_strictMono
      refine ⟨L, P, hL, ?_, ?_⟩
      · intro i
        exact ⟨StrongSubtree.refines_refl (P i), rfl, hP i⟩
      · intro A hA
        simp at hA
  | @insert A sets hnot ih =>
      obtain ⟨M₀, R₀, hM₀, hR₀, hRest⟩ := ih
      obtain ⟨M₁, R₁, hM₁, hR₁, hA⟩ :=
        exists_heterogeneousUniformConeStabilization
          R₀ hd n M₀ (fun i => (hR₀ i).2.2) hAll A
      have hR : ∀ i, (R₁ i).Refines (P i) ∧
          r n (R₁ i) = r n (P i) ∧
          (R₁ i).levels = M₁ := by
        intro i
        exact ⟨((hR₁ i).1).trans (hR₀ i).1,
          ((hR₁ i).2.1).trans (hR₀ i).2.1,
          (hR₁ i).2.2⟩
      refine ⟨M₁, R₁, hM₁, hR, ?_⟩
      intro B hB
      rcases Finset.mem_insert.mp hB with heq | hb
      · subst B
        exact hA
      · exact HeterogeneousUniformConeConstant.refinement
          R₀ R₁ hd M₀ M₁
          (fun i => (hR₀ i).2.2)
          (fun i => (hR₁ i).2.2)
          (fun i => (hR₁ i).1)
          n (fun i => (hR₁ i).2.1)
          B (hRest B hb)

end GeneralTree
end Milliken
