import Milliken.GeneralTree.HeterogeneousProtectedFusionLimit
import Milliken.GeneralTree.HeterogeneousStabilization
import Milliken.GeneralTree.ThinningStrong

/-!
# Stabilization passes to synchronized protected fusion limits

Suppose a sequence of synchronized (d+1)-coordinate strong-tree
families is descending and stage n+1 preserves the first n+1
finite source approximations of stage n. Assume each finite
stage N satisfies Todorčević's stabilization identity for all
last-coordinate source levels t < N.

The already proved *noncircular* strong-tree code reconstruction
gives a synchronized limit family. On any selected limit level l,
all coordinate nodes are exactly the corresponding nodes of
stage l+1; every last-coordinate node on level t<l has the
same stage-l+1 identity. Even the retained truncations at
t+1 agree, because they are the unique ancestors on exactly
the same protected source level.

Consequently stabilization at finite stage l+1 implies
stabilization on the infinite limiting family. This theorem
requires no Ramsey premise, HDHL hypothesis, A4, uniform degree
bound or fixed word alphabet.

The separate remaining construction is a cumulative sequence
of finite stages satisfying the stabilization hypotheses.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Every source level n in a protected fusion limit agrees with
that of *any* finite stage k>n, not just stage n+1. -/
theorem HeterogeneousProtectedFusion.limit_sourceLevel_eq_stage
    (S : HeterogeneousProtectedFusion U d)
    (i : Fin d) {n k : ℕ} (hnk : n < k) :
    (S.limit i).sourceLevel n = (S.family k i).sourceLevel n := by
  have hstable :
      r (n + 1) (S.family k i) =
        r (n + 1) (S.family (n + 1) i) :=
    generalFusionApprox_stable (fun m => S.family m i)
      (fun m => S.protects m i)
      (Nat.succ_le_of_lt hnk)
  calc
    (S.limit i).sourceLevel n =
        (S.family (n + 1) i).sourceLevel n :=
      S.limit_sourceLevel i n
    _ = maxLevel (r (n + 1) (S.family (n + 1) i)) :=
      (maxLevel_r_succ (S.family (n + 1) i) n).symm
    _ = maxLevel (r (n + 1) (S.family k i)) := by
      rw [hstable]
    _ = (S.family k i).sourceLevel n :=
      maxLevel_r_succ (S.family k i) n

/-- Stabilization at one specified last-coordinate source level. -/
def HeterogeneousStabilizedAt
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (t : ℕ) : Prop :=
  ∀ (l : ℕ) (y : U),
    y ∈ (P (Fin.last d)).sourceLevel t →
    ∀ (x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) l)
      (htl : t < l),
      (x.1 ∈ heterogeneousLastSection Q y ↔
        (heterogeneousTruncate
          (fun i : Fin d => P i.castSucc)
          (Nat.succ_le_of_lt htl) x).1 ∈
          heterogeneousLastSection Q y)

/-- Every full stabilization identity can be checked one
last-coordinate selected source level at a time. -/
theorem heterogeneousStabilized_iff_at
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) :
    HeterogeneousStabilized P Q ↔
      ∀ t : ℕ, HeterogeneousStabilizedAt P Q t := by
  constructor
  · intro h t l y hy x htl
    exact h t l y hy x htl
  · intro h t l y hy x htl
    exact h t l y hy x htl

/-- Each finite stage stabilizing the last-coordinate levels
strictly below its stage number implies full stabilization of
the synchronized infinite protected fusion limit. -/
theorem HeterogeneousProtectedFusion.limit_stabilized
    (S : HeterogeneousProtectedFusion U (d + 1))
    (Q : Set (Fin (d + 1) → U))
    (hstage : ∀ N t, t < N →
      HeterogeneousStabilizedAt (S.family N) Q t) :
    HeterogeneousStabilized S.limit Q := by
  classical
  intro t l y hy x htl
  let N : ℕ := l + 1
  let Front : Fin d → StrongSubtree U :=
    fun i => S.limit i.castSucc
  let Stage : Fin d → StrongSubtree U :=
    fun i => S.family N i.castSucc
  have hyStage :
      y ∈ (S.family N (Fin.last d)).sourceLevel t := by
    rw [← S.limit_sourceLevel_eq_stage
      (Fin.last d) (show t < N by dsimp [N]; omega)]
    exact hy
  have hxStage (i : Fin d) :
      x.1 i ∈ (Stage i).sourceLevel l := by
    change x.1 i ∈ (S.family N i.castSucc).sourceLevel l
    rw [← S.limit_sourceLevel_eq_stage
      i.castSucc (show l < N by dsimp [N]; omega)]
    exact x.2 i
  let xs : HeterogeneousLevelTuple Stage l := ⟨x.1, hxStage⟩
  have hq : t + 1 ≤ l := Nat.succ_le_of_lt htl
  have hqN : t + 1 < N := by dsimp [N]; omega
  have hsame (i : Fin d) :
      (Front i).sourceLevel (t + 1) =
        (Stage i).sourceLevel (t + 1) :=
    S.limit_sourceLevel_eq_stage i.castSucc hqN
  have htrunc :
      (heterogeneousTruncate Front hq x).1 =
        (heterogeneousTruncate Stage hq xs).1 := by
    funext i
    let a := (Front i).sourceAncestorAt hq (x.2 i)
    let b := (Stage i).sourceAncestorAt hq (xs.2 i)
    have ha := (Front i).sourceAncestorAt_spec hq (x.2 i)
    have hb := (Stage i).sourceAncestorAt_spec hq (xs.2 i)
    have haStage : a ∈ (Stage i).sourceLevel (t + 1) := by
      rw [← hsame i]
      exact ha.1
    have heqRank : U.level a = U.level b :=
      haStage.2.trans hb.1.2.symm
    exact U.eq_of_common_descendant_of_level_eq
      ha.2 hb.2 heqRank
  have hiff := (hstage N t (by dsimp [N]; omega))
    l y hyStage xs htl
  change
    (x.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate Stage hq xs).1 ∈
        heterogeneousLastSection Q y) at hiff
  change
    (x.1 ∈ heterogeneousLastSection Q y ↔
      (heterogeneousTruncate Front hq x).1 ∈
        heterogeneousLastSection Q y)
  rw [htrunc]
  exact hiff

end GeneralTree
end Milliken
