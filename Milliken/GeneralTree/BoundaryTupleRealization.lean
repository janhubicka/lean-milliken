import Milliken.GeneralTree.BoundaryGraftStrong

/-!
# Realising every synchronized boundary tuple as one finite strong extension

Any finite tuple of nodes selected at one common level of the actual
source-boundary successor cones is the next source level of a genuine
strong refinement retaining the old finite stem. The realization is
built from the inverse heterogeneous graft and the strong cone rooted
at each selected tuple entry.

The statement applies to arbitrary pruned locally finitely branching
ambient trees; no degree bound, regular alphabet, or unproved HL axiom
enters the construction.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- All coordinates of a finite boundary tuple belong to a single
source level of their corresponding actual T-boundary cones. -/
def IsSynchronizedBoundaryTuple
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U) : Prop :=
  ∃ k : ℕ, ∀ i, x i ∈ (boundaryCones T n i).sourceLevel k

/-- Construct a genuine infinite strong refinement of T whose
first new source level is exactly the given finite tuple. -/
theorem exists_boundaryTuple_realization
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U)
    (hx : IsSynchronizedBoundaryTuple T n x) :
    ∃ G : StrongSubtree U,
      G.Refines T ∧ r n G = r n T ∧
      G.sourceLevel n = Set.range x := by
  classical
  obtain ⟨k, hxk⟩ := hx
  let F : SourceBoundary T n → StrongSubtree U :=
    fun i => (boundaryCones T n i).coneStrong k (x i) (hxk i)
  let M : ℕ → ℕ := fun j => T.levels (n + (k + j))
  have hF : ∀ i, (F i).Refines (boundaryCones T n i) := by
    intro i
    exact (boundaryCones T n i).coneStrong_refines k (x i) (hxk i)
  have hlevels : ∀ i, (F i).levels = M := by
    intro i
    funext j
    rfl
  have hM : StrictMono M := by
    intro a b hab
    exact T.levels_strictMono (by dsimp [M]; omega)
  let G : StrongSubtree U := T.boundaryGraftStrong n F M hF hlevels hM
  refine ⟨G, T.boundaryGraftStrong_refines n F M hF hlevels hM,
    T.boundaryGraftStrong_approx n F M hF hlevels hM, ?_⟩
  calc
    G.sourceLevel n =
        Set.range (fun i : SourceBoundary T n => (F i).root) :=
      T.boundaryGraftStrong_sourceLevel_at n F M hF hlevels hM
    _ = Set.range x := by
      have hfuns : (fun i : SourceBoundary T n => (F i).root) = x := by
        funext i
        rfl
      rw [hfuns]

/-- A canonical realization of any synchronized finite boundary
vector. Its carrier can be computed without unfolding this choice. -/
noncomputable def boundaryTupleRealization
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U)
    (hx : IsSynchronizedBoundaryTuple T n x) : StrongSubtree U :=
  Classical.choose (exists_boundaryTuple_realization T n x hx)

/-- The canonical chosen realization is a strong refinement of T,
retaining the prescribed initial finite source levels. -/
theorem boundaryTupleRealization_spec
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U)
    (hx : IsSynchronizedBoundaryTuple T n x) :
    (boundaryTupleRealization T n x hx).Refines T ∧
      r n (boundaryTupleRealization T n x hx) = r n T ∧
      (boundaryTupleRealization T n x hx).sourceLevel n =
        Set.range x :=
  Classical.choose_spec (exists_boundaryTuple_realization T n x hx)

/-- The height-(n+1) finite approximation realized by a
synchronized boundary tuple. -/
noncomputable def boundaryTupleApprox
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U)
    (hx : IsSynchronizedBoundaryTuple T n x) :
    SFinite U (n + 1) :=
  r (n + 1) (boundaryTupleRealization T n x hx)

/-- The new one-step carrier is precisely the old finite stem
plus the image of the tuple. This is independent of realization
and of the chosen common source index. -/
theorem boundaryTupleApprox_carrier
    (T : StrongSubtree U) (n : ℕ)
    (x : SourceBoundary T n → U)
    (hx : IsSynchronizedBoundaryTuple T n x) :
    (boundaryTupleApprox T n x hx).carrier =
      (r n T).carrier ∪ Set.range x := by
  let G : StrongSubtree U := boundaryTupleRealization T n x hx
  have hspec := boundaryTupleRealization_spec T n x hx
  change (r (n + 1) G).carrier =
    (r n T).carrier ∪ Set.range x
  calc
    (r (n + 1) G).carrier = G.initialPart n ∪ G.sourceLevel n :=
      G.initialPart_succ n
    _ = (r n T).carrier ∪ Set.range x := by
      rw [hspec.2.2]
      exact congrArg (fun a : SFinite U n =>
        a.carrier ∪ Set.range x) hspec.2.1

end GeneralTree
end Milliken
