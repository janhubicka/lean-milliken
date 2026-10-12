import Milliken.GeneralTree.ProtectedBoundaryBijection
import Milliken.GeneralTree.HeterogeneousFiniteStabilization

/-!
# Uniform stabilization of every finite boundary cone

The finite-requirement fusion can stabilize an arbitrary finite list
of pairs (product set, boundary tuple). Apply it to *all* source-n
tuples of the input product, a finite set despite arbitrarily varying
local branching degrees.

A protected refinement induces a bijection between its source-n
boundary and the original source-n boundary. Hence every final
source-n tuple is the unique lift of an old tuple. The finite
requirement for that old tuple has its stabilized cone based at
precisely this new tuple, so the entire new source-n product
is covered, not merely an unspecified collection of cones.

This is the uniform finite-stage stabilization theorem needed
to pass from individual cone requirements to Todorčević's (*).
It assumes front-dimensional HDHL for all genuine front factors,
not HDHL in the higher dimension.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- All product boundary cones at source index n have constant
membership in A at all subsequent synchronized selected levels. -/
def HeterogeneousUniformConeConstant
    (P : Fin d → StrongSubtree U)
    (A : Set (Fin d → U)) (n : ℕ) : Prop :=
  ∀ base : HeterogeneousLevelTuple P n,
    HeterogeneousConeConstant P A base

/-- Uniformize the finite local stabilization requirements
over every tuple of the actual finite source-level-n product. -/
theorem exists_heterogeneousUniformConeStabilization
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (n : ℕ) (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (A : Set (Fin d → U)) :
    ∃ (M : ℕ → ℕ) (R : Fin d → StrongSubtree U),
      StrictMono M ∧
      (∀ i, (R i).Refines (P i) ∧
        r n (R i) = r n (P i) ∧
        (R i).levels = M) ∧
      HeterogeneousUniformConeConstant R A n := by
  classical
  letI : Fintype (HeterogeneousLevelTuple P n) := Fintype.ofFinite _
  let req : HeterogeneousLevelTuple P n →
      HeterogeneousLocalRequirement P n :=
    fun b => ⟨A, b⟩
  let reqs : List (HeterogeneousLocalRequirement P n) :=
    (Finset.univ : Finset (HeterogeneousLevelTuple P n)).toList.map req
  obtain ⟨S⟩ :=
    exists_heterogeneousFiniteStabilization
      P n hd L hP hAll reqs
  let i0 : Fin d := ⟨0, hd⟩
  have hM : StrictMono S.levels := by
    rw [← S.synchronized i0]
    exact (S.S i0).levels_strictMono
  refine ⟨S.levels, S.S, hM, ?_, ?_⟩
  · intro i
    exact ⟨S.refines i, S.prefix_eq i, S.synchronized i⟩
  · intro bNew
    let e (i : Fin d) :
        SourceBoundary (P i) n ≃ SourceBoundary (S.S i) n :=
      (P i).protectedBoundaryEquiv
        (S.S i) (S.refines i) (S.prefix_eq i)
    let oldSrc (i : Fin d) : SourceBoundary (P i) n :=
      (e i).symm ⟨bNew.1 i, bNew.2 i⟩
    let old : HeterogeneousLevelTuple P n :=
      ⟨fun i => (oldSrc i).1, fun i => (oldSrc i).2⟩
    have hOldDesc : ∀ i, old.1 i ≤ bNew.1 i := by
      intro i
      have hLift :
          (oldSrc i).1 ≤
            ((P i).protectedBoundaryLift
              (S.S i) (S.refines i) (S.prefix_eq i)
              (oldSrc i)).1 :=
        (P i).protectedBoundaryLift_above
          (S.S i) (S.refines i) (S.prefix_eq i) (oldSrc i)
      have hEq :
          (P i).protectedBoundaryLift
            (S.S i) (S.refines i) (S.prefix_eq i)
            (oldSrc i) =
          (⟨bNew.1 i, bNew.2 i⟩ : SourceBoundary (S.S i) n) := by
        change (e i) ((e i).symm ⟨bNew.1 i, bNew.2 i⟩) =
          ⟨bNew.1 i, bNew.2 i⟩
        exact (e i).apply_symm_apply _
      rw [hEq] at hLift
      exact hLift
    have hReq : req old ∈ reqs := by
      dsimp [reqs]
      exact List.mem_map.mpr
        ⟨old, Finset.mem_toList.mpr (Finset.mem_univ old), rfl⟩
    obtain ⟨b, hOldB, hConst⟩ :=
      S.satisfies (req old) hReq
    have hEq : b = bNew := by
      apply Subtype.ext
      funext i
      let u := (P i).existsUnique_sourceLevel_lift_of_refines
        (S.S i) (S.refines i) (S.prefix_eq i) (old.2 i)
      have hbEq :
          b.1 i = Classical.choose u :=
        (Classical.choose_spec u).2 (b.1 i)
          ⟨b.2 i, hOldB i⟩
      have hnEq :
          bNew.1 i = Classical.choose u :=
        (Classical.choose_spec u).2 (bNew.1 i)
          ⟨bNew.2 i, hOldDesc i⟩
      exact hbEq.trans hnEq.symm
    simpa only [req] using (hEq ▸ hConst)

end GeneralTree
end Milliken
