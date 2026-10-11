import Milliken.GeneralTree.BoundaryBijection

/-!
# Encoding every fixed-stem one-step approximation by an HL boundary tuple

For a strong refinement S⊆T preserving r_n(T), the checked finite
ancestor bijection identifies S's nth source level with the genuine
finite set of T-boundary successor cones. Its inverse gives a tuple
of selected S-nodes, one in each cone, all on the *same* T-selected
ambient level indexed by m-n, where m is the n-th refinement index.

The image of the tuple is exactly S's nth selected source level.
Therefore the height-(n+1) approximation r_(n+1)(S) is the union
of the fixed height-n stem with that finite tuple image.

These are the source-faithful decoding lemmas needed to turn
the canonical A.4 coloring into a coloring of the
Halpern–Läuchli level product. No HL theorem is asserted here.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The unique canonical ancestor bijection when the preceding
finite stem is fixed. -/
noncomputable def boundaryEquiv
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (hStem : r n S = r n T) :
    SourceBoundary S n ≃ SourceBoundary T n :=
  Equiv.ofBijective (S.boundaryAncestor T hST n)
    (S.boundaryAncestor_bijective_of_sameStem T hST n hStem)

/-- The actual common-level tuple of selected representatives,
indexed by T's finite nth source boundary. -/
noncomputable def boundaryTuple
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (hStem : r n S = r n T) :
    SourceBoundary T n → U :=
  fun i => ((S.boundaryEquiv T hST n hStem).symm i).1

/-- The selected tuple occupies precisely one node in each
strong T-boundary cone at one common source level. -/
theorem boundaryTuple_mem_cone
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (hStem : r n S = r n T)
    (i : SourceBoundary T n) :
    S.boundaryTuple T hST n hStem i ∈
      (boundaryCones T n i).sourceLevel
        (S.refinementIndex T hST n - n) := by
  let E := S.boundaryEquiv T hST n hStem
  let zS : SourceBoundary S n := E.symm i
  have hInv : S.boundaryAncestor T hST n zS = i := by
    simpa only [boundaryEquiv, Equiv.ofBijective_apply] using
      (E.apply_symm_apply i)
  have hAncestor : i.1 ≤ zS.1 := by
    rw [← hInv]
    exact S.boundaryAncestor_le T hST n zS
  have hSource :
      zS.1 ∈ T.sourceLevel (S.refinementIndex T hST n) :=
    S.sourceLevel_subset_refinementIndex T hST n zS.2
  have hIndex : n + (S.refinementIndex T hST n - n) =
      S.refinementIndex T hST n := by
    have hle := S.le_refinementIndex T hST n
    omega
  change zS.1 ∈
    (boundaryCones T n i).sourceLevel
      (S.refinementIndex T hST n - n)
  rw [boundaryCones_sourceLevel]
  refine ⟨⟨hSource.1, ?_⟩, hAncestor⟩
  simpa only [hIndex] using hSource.2

/-- The image of the canonical boundary tuple is exactly
the final new selected source level of the refinement. -/
theorem boundaryTuple_range
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (hStem : r n S = r n T) :
    Set.range (S.boundaryTuple T hST n hStem) =
      S.sourceLevel n := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ((S.boundaryEquiv T hST n hStem).symm i).2
  · intro hz
    let zS : SourceBoundary S n := ⟨z, hz⟩
    let E := S.boundaryEquiv T hST n hStem
    refine ⟨E zS, ?_⟩
    change (E.symm (E zS)).1 = z
    rw [E.symm_apply_apply]

/-- Every one-step approximation of the fixed canonical stem is
exactly that stem together with the image of its common-level
boundary tuple. No homogeneous branching is assumed. -/
theorem approx_succ_carrier_eq_boundaryTuple
    (S T : StrongSubtree U) (hST : S.Refines T)
    (n : ℕ) (hStem : r n S = r n T) :
    (r (n + 1) S).carrier =
      (r n T).carrier ∪
        Set.range (S.boundaryTuple T hST n hStem) := by
  calc
    (r (n + 1) S).carrier =
        S.initialPart n ∪ S.sourceLevel n :=
      S.initialPart_succ n
    _ = (r n T).carrier ∪
        Set.range (S.boundaryTuple T hST n hStem) := by
      rw [← S.boundaryTuple_range T hST n hStem]
      exact congrArg (fun c : SFinite U n =>
        c.carrier ∪
          Set.range (S.boundaryTuple T hST n hStem)) hStem

end StrongSubtree
end GeneralTree
end Milliken
