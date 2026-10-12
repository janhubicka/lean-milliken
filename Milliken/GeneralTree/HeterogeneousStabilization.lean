import Milliken.GeneralTree.HeterogeneousTruncation
import Milliken.GeneralTree.HeterogeneousSections

/-!
# Stabilized product sections over genuinely heterogeneous trees

The stabilization property (*) in Todorčević's Lemma 3.15 uses
truncation of a front-coordinate tuple at the source level just
after the fixed last-coordinate node. For arbitrary strong trees,
the earlier coordinatewise ancestors replace literal List.take.

This module states precisely this stabilization invariant and proves
that its section membership and avoidance are preserved when a later
matrix is refined above an earlier level matrix. It is a formal
implication from the **explicit stabilization hypothesis**, not a
claim that arbitrary product sets have already been stabilized.
Constructing a stabilized refinement is the next fusion obligation.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Stabilization (*) for the d+1 product of arbitrary locally
finitely branching strong coordinate trees: membership in the
last-coordinate section at y is determined by truncating the
front-coordinate vector to one source level after y. -/
def HeterogeneousStabilized
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) : Prop :=
  ∀ (t l : ℕ)
    (y : U) (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) l)
    (htl : t < l),
      (x.1 ∈ heterogeneousLastSection Q y ↔
        (heterogeneousTruncate
          (fun i : Fin d => P i.castSucc)
          (Nat.succ_le_of_lt htl) x).1 ∈
          heterogeneousLastSection Q y)

/-- Stabilization is preserved by complementing the color class. -/
theorem HeterogeneousStabilized.compl
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hstab : HeterogeneousStabilized P Q) :
    HeterogeneousStabilized P Qᶜ := by
  intro t l y hy x htl
  change
    (¬ (x.1 ∈ heterogeneousLastSection Q y)) ↔
      (¬ ((heterogeneousTruncate
        (fun i : Fin d => P i.castSucc)
        (Nat.succ_le_of_lt htl) x).1 ∈
        heterogeneousLastSection Q y))
  exact (hstab t l y hy x htl).not

namespace HeterogeneousMatrix

/-- Stabilized section membership is preserved under coordinatewise
refinement of a later matrix B above an earlier level matrix A. -/
theorem refineOver_preserves_section
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hstab : HeterogeneousStabilized P Q)
    (hd : 0 < d)
    {A B : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc)}
    {t lA lB : ℕ}
    (y : U) (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (hAlevel : A.OnLevel lA)
    (hBlevel : B.OnLevel lB)
    (htA : t < lA)
    (hAsub : A.carrier ⊆ heterogeneousLastSection Q y) :
    (A.refineOver B).carrier ⊆
      heterogeneousLastSection Q y := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  intro z hz
  obtain ⟨a, haA, haz⟩ :=
    exists_predecessor_of_mem_refineOver hz
  have hzB : z ∈ B.carrier :=
    refineOver_carrier_subset_right A B hz
  have haOn : ∀ i, a i ∈ (Front i).sourceLevel lA := by
    intro i
    exact hAlevel i (a i) (haA i)
  have hzOn : ∀ i, z i ∈ (Front i).sourceLevel lB := by
    intro i
    exact hBlevel i (z i) (hzB i)
  let i0 : Fin d := ⟨0, hd⟩
  have hlAB : lA ≤ lB := by
    have hrank : (Front i0).levels lA ≤ (Front i0).levels lB := by
      calc
        (Front i0).levels lA = U.level (a i0) :=
          (haOn i0).2.symm
        _ ≤ U.level (z i0) := U.level_mono (haz i0)
        _ = (Front i0).levels lB := (hzOn i0).2
    by_contra hbad
    have hlt : lB < lA := Nat.lt_of_not_ge hbad
    have hs := (Front i0).levels_strictMono hlt
    omega
  have htB : t < lB := htA.trans_le hlAB
  let av : HeterogeneousLevelTuple Front lA := ⟨a, haOn⟩
  let zv : HeterogeneousLevelTuple Front lB := ⟨z, hzOn⟩
  have htrunc :
      heterogeneousTruncate Front (Nat.succ_le_of_lt htA) av =
        heterogeneousTruncate Front (Nat.succ_le_of_lt htB) zv := by
    exact heterogeneousTruncate_eq_of_le
      Front (Nat.succ_le_of_lt htA) hlAB av zv haz
  have hAsection : av.1 ∈ heterogeneousLastSection Q y :=
    hAsub haA
  have hAtrunc :
      (heterogeneousTruncate Front
        (Nat.succ_le_of_lt htA) av).1 ∈
        heterogeneousLastSection Q y :=
    (hstab t lA y hy av htA).mp hAsection
  have hZtrunc :
      (heterogeneousTruncate Front
        (Nat.succ_le_of_lt htB) zv).1 ∈
        heterogeneousLastSection Q y := by
    rw [← htrunc]
    exact hAtrunc
  exact (hstab t lB y hy zv htB).mpr hZtrunc

/-- Stabilization also propagates section *avoidance* through
a later heterogeneous matrix refinement. -/
theorem refineOver_avoids_section
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hstab : HeterogeneousStabilized P Q)
    (hd : 0 < d)
    {A B : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc)}
    {t lA lB : ℕ}
    (y : U) (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (hAlevel : A.OnLevel lA)
    (hBlevel : B.OnLevel lB)
    (htA : t < lA)
    (hAavoid : A.carrier ⊆
      (heterogeneousLastSection Q y)ᶜ) :
    (A.refineOver B).carrier ⊆
      (heterogeneousLastSection Q y)ᶜ := by
  have hcomp : HeterogeneousStabilized P Qᶜ :=
    HeterogeneousStabilized.compl P Q hstab
  have hAsub : A.carrier ⊆ heterogeneousLastSection Qᶜ y := by
    simpa only [heterogeneousLastSection_compl] using hAavoid
  have hres :=
    refineOver_preserves_section
      P Qᶜ hcomp hd y hy hAlevel hBlevel htA hAsub
  simpa only [heterogeneousLastSection_compl] using hres

end HeterogeneousMatrix
end GeneralTree
end Milliken
