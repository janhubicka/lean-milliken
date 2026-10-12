import Milliken.GeneralTree.HeterogeneousCommonIndex
import Milliken.GeneralTree.ThinningApprox

/-!
# Completing synchronized front refinements with a last coordinate

Let P be a synchronized (d+1)-dimensional family of arbitrary
locally finitely branching strong trees, d>0. Suppose its front
d factors have been synchronously refined to one common ambient
level sequence M while preserving their height-(n+1) finite
approximations.

The front selected levels determine one strictly increasing source
index map f of the original family, necessarily fixing indices
0,...,n. Thin the last factor along exactly f. This produces a
genuine last-coordinate strong refinement with level map M and
the same protected (n+1)-stem, without touching any prior
last-coordinate stabilization requirements.

No Halpern--Läuchli premise, fixed alphabet, global branching
bound or combinatorial axiom is involved.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Any synchronized front refinement preserving its first n+1
source levels determines a canonical last-factor thinning to
exactly the same ambient levels, preserving its first n+1
source levels too. -/
theorem exists_synchronizedLastRefinement_of_front
    (P : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (F : Fin d → StrongSubtree U)
    (hF : ∀ i, (F i).Refines (P i.castSucc) ∧
      (F i).levels = M)
    (n : ℕ)
    (hprefix : ∀ i,
      r (n + 1) (F i) = r (n + 1) (P i.castSucc)) :
    ∃ K : StrongSubtree U,
      K.Refines (P (Fin.last d)) ∧
      K.levels = M ∧
      r (n + 1) K = r (n + 1) (P (Fin.last d)) := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  have hFront : ∀ i, (Front i).levels = L :=
    fun i => hP i.castSucc
  obtain ⟨f, hf, hMf, _⟩ :=
    exists_synchronizedRefinement_commonIndex
      Front F hd L M hFront
      (fun i => (hF i).2)
      (fun i => (hF i).1)
  let i0 : Fin d := ⟨0, hd⟩
  have hL : StrictMono L := by
    rw [← hP i0.castSucc]
    exact (P i0.castSucc).levels_strictMono
  have hfixed : ∀ k : ℕ, k ≤ n → f k = k := by
    intro k hk
    have heq :
        r (k + 1) (F i0) =
          r (k + 1) (P i0.castSucc) :=
      r_coherent_le (F i0) (P i0.castSucc)
        (n + 1) (hprefix i0) (k + 1) (by omega)
    have hSource :
        (F i0).sourceLevel k =
          (P i0.castSucc).sourceLevel k := by
      calc
        (F i0).sourceLevel k =
            maxLevel (r (k + 1) (F i0)) :=
          (maxLevel_r_succ (F i0) k).symm
        _ = maxLevel (r (k + 1) (P i0.castSucc)) := by rw [heq]
        _ = (P i0.castSucc).sourceLevel k :=
          maxLevel_r_succ (P i0.castSucc) k
    obtain ⟨x, hx⟩ := (F i0).sourceLevel_nonempty k
    have hxP : x ∈ (P i0.castSucc).sourceLevel k := by
      rw [← hSource]
      exact hx
    have heqIndex : L (f k) = L k := by
      calc
        L (f k) = M k := (hMf k).symm
        _ = (F i0).levels k := (congrFun (hF i0).2 k).symm
        _ = U.level x := hx.2.symm
        _ = (P i0.castSucc).levels k := hxP.2
        _ = L k := congrFun (hP i0.castSucc) k
    exact hL.injective heqIndex
  have hf0 : f 0 = 0 := hfixed 0 (Nat.zero_le n)
  let K : StrongSubtree U :=
    (P (Fin.last d)).thinStrong f hf hf0
  have hLevels : K.levels = M := by
    change (fun k => (P (Fin.last d)).levels (f k)) = M
    funext k
    exact (congrFun (hP (Fin.last d)) (f k)).trans
      (hMf k).symm
  refine ⟨K, (P (Fin.last d)).thinStrong_refines f hf hf0,
    hLevels, ?_⟩
  exact (P (Fin.last d)).thinStrong_approx_succ_of_fixed
    f hf hf0 n hfixed

end GeneralTree
end Milliken
