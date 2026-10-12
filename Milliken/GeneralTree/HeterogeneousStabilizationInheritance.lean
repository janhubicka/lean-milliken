import Milliken.GeneralTree.HeterogeneousFullProductStage
import Milliken.GeneralTree.HeterogeneousCommonIndex

/-!
# Inheritance of heterogeneous stabilization at previous levels

In the cumulative HDHL stabilization construction stage n+1
preserves the first n+1 source levels. A stabilization identity
already established at a last-coordinate level t<n must survive.

For that earlier t, the source-t node in the last factor and the
source-(t+1) ancestor in each front factor lie in the protected
prefix. A synchronized refinement has one strictly increasing
source-index map; its later selected level tuples therefore belong
to some common older source level. The old stabilization identity
applies there, and uniqueness of the protected truncation ancestor
identifies old and new truncations.

No Ramsey assumption, new HDHL input, or global branching bound
is needed for this inheritance step.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A synchronized full-product strong refinement preserving the
first t+2 finite source levels retains every stabilization identity
at last-coordinate source index t. -/
theorem HeterogeneousStabilizedAt.refinement
    (P R : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hR : ∀ i, (R i).levels = M)
    (hRP : ∀ i, (R i).Refines (P i))
    (Q : Set (Fin (d + 1) → U))
    (t : ℕ)
    (hprefix : ∀ i, r (t + 2) (R i) = r (t + 2) (P i))
    (hstab : HeterogeneousStabilizedAt P Q t) :
    HeterogeneousStabilizedAt R Q t := by
  classical
  let FrontP : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  let FrontR : Fin d → StrongSubtree U :=
    fun i => R i.castSucc
  obtain ⟨f, hf, _, hsub⟩ :=
    exists_synchronizedRefinement_commonIndex
      FrontP FrontR hd L M
      (fun i => hP i.castSucc)
      (fun i => hR i.castSucc)
      (fun i => hRP i.castSucc)
  have hSame (i : Fin (d + 1)) (k : ℕ) (hk : k ≤ t + 1) :
      (R i).sourceLevel k = (P i).sourceLevel k := by
    have heq :
        r (k + 1) (R i) = r (k + 1) (P i) :=
      r_coherent_le (R i) (P i)
        (t + 2) (hprefix i) (k + 1) (by omega)
    calc
      (R i).sourceLevel k = maxLevel (r (k + 1) (R i)) :=
        (maxLevel_r_succ (R i) k).symm
      _ = maxLevel (r (k + 1) (P i)) := by rw [heq]
      _ = (P i).sourceLevel k := maxLevel_r_succ (P i) k
  intro l y hy x htl
  have hyP :
      y ∈ (P (Fin.last d)).sourceLevel t := by
    rw [← hSame (Fin.last d) t (by omega)]
    exact hy
  have hfl : l ≤ f l := hf.id_le l
  have htfl : t < f l := htl.trans_le hfl
  let oldX : HeterogeneousLevelTuple FrontP (f l) :=
    ⟨x.1, fun i => hsub l i (x.2 i)⟩
  have hSameFront (i : Fin d) :
      (FrontR i).sourceLevel (t + 1) =
        (FrontP i).sourceLevel (t + 1) :=
    hSame i.castSucc (t + 1) (by omega)
  have htrunc :
      (heterogeneousTruncate FrontR
        (Nat.succ_le_of_lt htl) x).1 =
      (heterogeneousTruncate FrontP
        (Nat.succ_le_of_lt htfl) oldX).1 := by
    funext i
    let a := (FrontR i).sourceAncestorAt
      (Nat.succ_le_of_lt htl) (x.2 i)
    let b := (FrontP i).sourceAncestorAt
      (Nat.succ_le_of_lt htfl) (oldX.2 i)
    have ha := (FrontR i).sourceAncestorAt_spec
      (Nat.succ_le_of_lt htl) (x.2 i)
    have hb := (FrontP i).sourceAncestorAt_spec
      (Nat.succ_le_of_lt htfl) (oldX.2 i)
    have haP : a ∈ (FrontP i).sourceLevel (t + 1) := by
      rw [← hSameFront i]
      exact ha.1
    have heq : U.level a = U.level b :=
      haP.2.trans hb.1.2.symm
    exact U.eq_of_common_descendant_of_level_eq ha.2 hb.2 heq
  have hold : oldX.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate FrontP
        (Nat.succ_le_of_lt htfl) oldX).1 ∈
        heterogeneousLastSection Q y :=
    hstab (f l) y hyP oldX htfl
  change
    (x.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate FrontR
        (Nat.succ_le_of_lt htl) x).1 ∈
        heterogeneousLastSection Q y)
  rw [htrunc]
  exact hold

end GeneralTree
end Milliken
