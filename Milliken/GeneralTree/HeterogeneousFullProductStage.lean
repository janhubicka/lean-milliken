import Milliken.GeneralTree.HeterogeneousUniformFiniteFamily
import Milliken.GeneralTree.HeterogeneousLastCoordinateSelector
import Milliken.GeneralTree.HeterogeneousStabilizationLimit

/-!
# One full-product heterogeneous stabilization stage

Fix a synchronized (d+1)-coordinate family of genuine strong trees,
a product set Q, and a last-coordinate source index t. Enumerate all
last-coordinate source-t nodes, a finite set even for arbitrary
node-dependent and unbounded finite branching, and simultaneously
stabilize their Q-sections on *every* front source-(t+1) cone using
the proved finite-family front-dimensional HDHL theorem.

The front refinement has a new common level map M and preserves
its height-(t+1) prefix. The protected last-coordinate selector
supplies a matching genuine strong thinning of the last factor
with exactly that level map and the same prefix.

The resulting synchronized full (d+1)-family satisfies the exact
Todorčević stabilization identity at last-coordinate source index t.
This is the finite-stage combinatorial construction, conditional
only on front-dimensional HDHL. No higher-dimensional HDHL or
strong-tree A4 assumption is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Stabilize the complete collection of sections at one
last-coordinate source level, extending the front refinement to
the last factor without changing the protected initial levels. -/
theorem exists_heterogeneousStabilizedAt_stage
    (P : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hAll : ∀ R : Fin d → StrongSubtree U,
      HasHeterogeneousHDHL R)
    (Q : Set (Fin (d + 1) → U))
    (t : ℕ) :
    ∃ (M : ℕ → ℕ)
      (S : Fin (d + 1) → StrongSubtree U),
      StrictMono M ∧
      (∀ i, (S i).Refines (P i) ∧
        r (t + 1) (S i) = r (t + 1) (P i) ∧
        (S i).levels = M) ∧
      HeterogeneousStabilizedAt S Q t := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  have hFront : ∀ i, (Front i).levels = L :=
    fun i => hP i.castSucc
  let Y : Finset U :=
    ((P (Fin.last d)).sourceLevel_finite t).toFinset
  let sections : Finset (Set (Fin d → U)) :=
    Y.image (fun y => heterogeneousLastSection Q y)
  obtain ⟨M, F, hM, hF, hconst⟩ :=
    exists_heterogeneousUniformConeStabilization_finset
      Front hd (t + 1) L hFront hAll sections
  obtain ⟨K, hKref, hKlevels, hKprefix⟩ :=
    exists_synchronizedLastRefinement_of_front
      P hd L M hP F
      (fun i => ⟨(hF i).1, (hF i).2.2⟩)
      t (fun i => (hF i).2.1)
  let S : Fin (d + 1) → StrongSubtree U :=
    fun i => Fin.lastCases K (fun j => F j) i
  have hSF : ∀ i : Fin d, S i.castSucc = F i := by
    intro i
    rfl
  have hSK : S (Fin.last d) = K := rfl
  have hComplete :
      ∀ i, (S i).Refines (P i) ∧
        r (t + 1) (S i) = r (t + 1) (P i) ∧
        (S i).levels = M := by
    intro i
    cases i using Fin.lastCases with
    | last =>
        exact ⟨hKref, hKprefix, hKlevels⟩
    | cast j =>
        exact hF j
  refine ⟨M, S, hM, hComplete, ?_⟩
  intro l y hy x htl
  have hLastLevel :
      (S (Fin.last d)).sourceLevel t =
        (P (Fin.last d)).sourceLevel t := by
    calc
      (S (Fin.last d)).sourceLevel t =
          maxLevel (r (t + 1) (S (Fin.last d))) :=
        (maxLevel_r_succ (S (Fin.last d)) t).symm
      _ = maxLevel (r (t + 1) (P (Fin.last d))) := by
        rw [(hComplete (Fin.last d)).2.1]
      _ = (P (Fin.last d)).sourceLevel t :=
        maxLevel_r_succ (P (Fin.last d)) t
  have hyP : y ∈ (P (Fin.last d)).sourceLevel t := by
    rw [← hLastLevel]
    exact hy
  have hyY : y ∈ Y := by
    simpa only [Y, Set.Finite.mem_toFinset] using hyP
  have hSection : heterogeneousLastSection Q y ∈ sections :=
    Finset.mem_image.mpr ⟨y, hyY, rfl⟩
  let X : HeterogeneousLevelTuple F l :=
    ⟨x.1, by
      intro i
      have hi := x.2 i
      simpa only [hSF i] using hi⟩
  let b : HeterogeneousLevelTuple F (t + 1) :=
    heterogeneousTruncate F (Nat.succ_le_of_lt htl) X
  have hC :
      HeterogeneousConeConstant F
        (heterogeneousLastSection Q y) b :=
    hconst (heterogeneousLastSection Q y) hSection b
  have hbx : ∀ i, b.1 i ≤ X.1 i :=
    heterogeneousTruncate_le F (Nat.succ_le_of_lt htl) X
  have hEq :=
    hC l X (Nat.succ_le_of_lt htl) hbx
  change
    (X.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate F
        (Nat.succ_le_of_lt htl) X).1 ∈
        heterogeneousLastSection Q y) at hEq
  change
    (x.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate
        (fun i : Fin d => S i.castSucc)
        (Nat.succ_le_of_lt htl) x).1 ∈
        heterogeneousLastSection Q y)
  exact hEq

end GeneralTree
end Milliken
