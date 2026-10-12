import Milliken.GeneralTree.ProtectedBoundaryLift
import Milliken.GeneralTree.BoundaryCones

/-!
# Covering the next selected source frontier under arbitrary refinement

If R strongly refines P and a node a is retained by both trees,
then *each* P-node on the next P-selected level directly below a
has a descendant on the next R-selected level below a.
The two source indices of a can differ.

The argument turns the actual successor cones rooted at a into
strong trees. These cones have the same root, so their first finite
approximations agree, regardless of how the input level maps differ.
We can therefore apply the already proved protected-boundary lift
at cone source index one.

This is the elementary geometric bridge behind transporting
somewhere-dense matrices through synchronized strong refinements.
It requires no fixed branching alphabet, global degree bound,
Ramsey theorem, or new axiom.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A strong refinement covers the complete next selected frontier
from any node simultaneously retained in the original tree. -/
theorem exists_next_sourceLevel_descendant_of_refines
    (P R : StrongSubtree U)
    (hRP : R.Refines P)
    {j q : ℕ} {a x : U}
    (haP : a ∈ P.sourceLevel j)
    (haR : a ∈ R.sourceLevel q)
    (hx : x ∈ P.sourceLevel (j + 1))
    (hax : a ≤ x) :
    ∃ y : U, y ∈ R.sourceLevel (q + 1) ∧ x ≤ y := by
  let Cp := boundaryCones P j ⟨a, haP⟩
  let Cr := boundaryCones R q ⟨a, haR⟩
  have hCrCp : Cr.Refines Cp := by
    intro z hz
    exact ⟨hRP hz.1, hz.2⟩
  have hroot : Cr.root = Cp.root := by
    simp [Cr, Cp]
  have happrox : r 1 Cr = r 1 Cp := by
    apply FiniteApprox.ext_carrier
    change Cr.initialPart 1 = Cp.initialPart 1
    calc
      Cr.initialPart 1 = Cr.sourceLevel 0 := by
        rw [Cr.initialPart_succ 0]
        simp [StrongSubtree.initialPart_zero]
      _ = {Cr.root} := Cr.sourceLevel_zero_eq_singleton
      _ = {Cp.root} := by rw [hroot]
      _ = Cp.sourceLevel 0 := Cp.sourceLevel_zero_eq_singleton.symm
      _ = Cp.initialPart 1 := by
        rw [Cp.initialPart_succ 0]
        simp [StrongSubtree.initialPart_zero]
  have hxCp : x ∈ Cp.sourceLevel 1 := by
    rw [show Cp.sourceLevel 1 =
        {z : U | z ∈ P.sourceLevel (j + 1) ∧ a ≤ z} from by
      simpa [Cp] using
        (boundaryCones_sourceLevel P j ⟨a, haP⟩ 1)]
    exact ⟨hx, hax⟩
  obtain ⟨y, hyCr, hxy⟩ :=
    Cp.exists_sourceLevel_lift_of_refines
      Cr hCrCp happrox hxCp
  have hyR : y ∈ R.sourceLevel (q + 1) := by
    have hlev := (boundaryCones_sourceLevel R q ⟨a, haR⟩ 1)
    change y ∈ (boundaryCones R q ⟨a, haR⟩).sourceLevel 1 at hyCr
    rw [hlev] at hyCr
    exact hyCr.1
  exact ⟨y, hyR, hxy⟩

end StrongSubtree
end GeneralTree
end Milliken
