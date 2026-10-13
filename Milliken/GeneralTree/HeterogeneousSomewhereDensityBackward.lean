import Milliken.GeneralTree.NextLevelRefinementCoverage
import Milliken.GeneralTree.HeterogeneousSomewhereDense
import Milliken.GeneralTree.HeterogeneousCommonIndex

/-!
# Backward transport of somewhere density along synchronized refinements

For synchronized families P and R of actual strong trees, with
R refining P, one strictly increasing source-index map f describes
every R selected level inside P. If a matrix N is somewhere dense
in R, choose a common earlier R source level q one step below
its density target and one node a_i on R level q in each old
base cone.

The source-(f(q)+1) frontier of P immediately above a_i is
covered by the source-(q+1) frontier of R. This is the previously
proved exact child-cone coverage lemma, requiring no fixed
alphabet or uniform branching degree. Density of N in R therefore
lifts to density of the same coordinate sets in P, above the
source-(f(q))-level product base a.

Consequently a colour class whose complement has no somewhere-dense
matrix in P retains this *negative* property on every synchronized
strong refinement R. This is the key missing inheritance needed
to apply the stabilized final HDHL induction theorem after fusion.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Lift an R-somewhere-dense product matrix to the containing
synchronized family P without changing its coordinate sets. -/
theorem heterogeneousSomewhereDense_lift_refinement
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (LP LR : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = LP)
    (hR : ∀ i, (R i).levels = LR)
    (hRP : ∀ i, (R i).Refines (P i))
    (N : HeterogeneousMatrix R)
    (hsome : N.SomewhereDense) :
    ∃ B : HeterogeneousMatrix P,
      B.SomewhereDense ∧ B.carrier = N.carrier := by
  classical
  obtain ⟨f, hf, _, hsub⟩ :=
    exists_synchronizedRefinement_commonIndex
      P R hd LP LR hP hR hRP
  obtain ⟨base, n, hbase, hDense⟩ := hsome
  let i0 : Fin d := ⟨0, hd⟩
  have hn : 0 < n := by
    obtain ⟨k, hk, _⟩ := hbase i0
    omega
  let q : ℕ := n - 1
  have hqn : q + 1 = n := by
    dsimp [q]
    omega
  have hex (i : Fin d) :
      ∃ a : U, a ∈ (R i).sourceLevel q ∧ base i ≤ a := by
    obtain ⟨k, hk, hb⟩ := hbase i
    have hkq : k ≤ q := by dsimp [q]; omega
    exact (R i).exists_sourceLevel_descendant hkq hb
  let a : Fin d → U := fun i => Classical.choose (hex i)
  have ha (i : Fin d) :
      a i ∈ (R i).sourceLevel q ∧ base i ≤ a i :=
    Classical.choose_spec (hex i)
  have haP (i : Fin d) :
      a i ∈ (P i).sourceLevel (f q) :=
    hsub q i (ha i).1
  let B : HeterogeneousMatrix P := {
    coord := N.coord
    coord_sub := by
      intro i z hz
      exact hRP i (N.coord_sub i hz)
  }
  have hBcarrier : B.carrier = N.carrier := rfl
  have hBsome : B.SomewhereDense := by
    refine ⟨a, f q + 1, ?_, ?_⟩
    · intro i
      exact ⟨f q, Nat.lt_succ_self _, haP i⟩
    · intro i x hx hax
      obtain ⟨z, hzR, hxz⟩ :=
        (P i).exists_next_sourceLevel_descendant_of_refines
          (R i) (hRP i) (haP i) (ha i).1 hx hax
      have hzN : z ∈ (R i).sourceLevel n := by
        rw [← hqn]
        exact hzR
      obtain ⟨y, hyN, hzy⟩ :=
        hDense i z hzN ((ha i).2.trans (hax.trans hxz))
      exact ⟨y, hyN, hxz.trans hzy⟩
  exact ⟨B, hBsome, hBcarrier⟩

/-- The negative somewhere-dense complement obstruction is inherited
by every synchronized strong refinement of the same family. -/
theorem heterogeneousNoSomewhereDense_refinement
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (LP LR : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = LP)
    (hR : ∀ i, (R i).levels = LR)
    (hRP : ∀ i, (R i).Refines (P i))
    (Q : Set (Fin d → U))
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ) :
    ¬ HeterogeneousContainsSomewhereDense R Qᶜ := by
  rintro ⟨N, hsome, hNbad⟩
  obtain ⟨B, hBsome, hcarrier⟩ :=
    heterogeneousSomewhereDense_lift_refinement
      P R hd LP LR hP hR hRP N hsome
  apply hno
  refine ⟨B, hBsome, ?_⟩
  intro x hx
  apply hNbad
  rw [← hcarrier]
  exact hx

end GeneralTree
end Milliken
