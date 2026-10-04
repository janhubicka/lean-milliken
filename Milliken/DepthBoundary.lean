import Milliken.Rebase
import Milliken.Graft
import Milliken.FinitizationOrder

/-!
# Minimal depth and the boundary level

For the carrier finitization used by the Lean development, minimality of
depth recovers the maximal-level clause of Todorčević's finitization (6.3).

Suppose `a = r_n(B ∘ H)` and the depth of `a` in `B` is `d`.
Every image under `H` of a source node below level `n` must lie below
level `d`.  If `n > 0`, minimality then forces the entire image of source
level `n-1` to be exactly ambient level `d-1`.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- Every node occurring in a depth-`d` approximation pulls back to a
source node of `B` below level `d`. -/
theorem factor_image_length_lt_depth
    [Finite ι] [Nonempty ι]
    {n d : ℕ} (a : Approx ι n)
    (B H : StrongEmbedding ι)
    (happrox :
      approx ι n (StrongEmbedding.comp B H) = a)
    (hd : (finitization (ι := ι)).HasDepth a B d)
    {s : Node ι} (hs : s.length < n) :
    (H.toFun s).length < d := by
  let sn : FiniteNode ι n := ⟨s, hs⟩
  have hval := congrArg
    (fun z : Approx ι n => z.1 sn) happrox
  change B.toFun (H.toFun s) = a.1 sn at hval
  have hxA :
      B.toFun (H.toFun s) ∈ approxCarrier a := by
    exact ⟨sn, hval.symm⟩
  have hmain :
      leFin (⟨n, a⟩ : (S ι).FiniteApprox)
        ((S ι).finiteApprox d B) := by
    exact hd.1
  rcases hmain.2 hxA with ⟨t, ht⟩
  change B.toFun t.1 = B.toFun (H.toFun s) at ht
  have heq : t.1 = H.toFun s := B.injective ht
  rw [← heq]
  exact t.2

/-- Minimal depth identifies the last source level with the last level of the
depth approximation. -/
theorem factor_top_level_eq_depth_pred
    [Finite ι] [Nonempty ι]
    {n d : ℕ} (hn : 0 < n)
    (a : Approx ι n)
    (B H : StrongEmbedding ι)
    (happrox :
      approx ι n (StrongEmbedding.comp B H) = a)
    (hd : (finitization (ι := ι)).HasDepth a B d)
    (q : LevelNode ι (n - 1)) :
    (H.toFun q.1).length = d - 1 := by
  have hmain :
      leFin (⟨n, a⟩ : (S ι).FiniteApprox)
        ((S ι).finiteApprox d B) := by
    exact hd.1
  have hnd : n ≤ d := hmain.1
  have hdpos : 0 < d := hn.trans_le hnd
  have hupper :
      (H.toFun q.1).length < d := by
    apply factor_image_length_lt_depth a B H happrox hd
    rw [q.2]
    omega
  by_contra hne
  have hqlt :
      (H.toFun q.1).length < d - 1 := by
    omega
  rcases H.level_witness with ⟨levels, hmono, hlevels⟩
  have hsource_le_image :
      n - 1 ≤ (H.toFun q.1).length := by
    rw [hlevels, q.2]
    exact StrictMono.id_le hmono (n - 1)
  have hnpred : n ≤ d - 1 := by
    omega
  have hcarrier :
      approxCarrier a ⊆ approxCarrier (approx ι (d - 1) B) := by
    rintro x ⟨s, rfl⟩
    have hsle : s.1.length ≤ q.1.length := by
      rw [q.2]
      omega
    have hHle :
        (H.toFun s.1).length ≤ (H.toFun q.1).length := by
      rw [hlevels, hlevels]
      exact hmono.monotone hsle
    have hHlt : (H.toFun s.1).length < d - 1 :=
      hHle.trans_lt hqlt
    let t : FiniteNode ι (d - 1) :=
      ⟨H.toFun s.1, hHlt⟩
    refine ⟨t, ?_⟩
    have hval := congrArg
      (fun z : Approx ι n => z.1 s) happrox
    exact hval
  have hbad :
      leFin (⟨n, a⟩ : (S ι).FiniteApprox)
        ((S ι).finiteApprox (d - 1) B) :=
    ⟨hnpred, hcarrier⟩
  exact (hd.2 (d - 1) (by omega)) hbad

/-- Consequently, all top-level factor images have the common depth boundary
level. -/
theorem factor_top_level_on_depth_pred
    [Finite ι] [Nonempty ι]
    {n d : ℕ} (hn : 0 < n)
    (a : Approx ι n)
    (B H : StrongEmbedding ι)
    (happrox :
      approx ι n (StrongEmbedding.comp B H) = a)
    (hd : (finitization (ι := ι)).HasDepth a B d) :
    ∀ q : LevelNode ι (n - 1),
      (H.toFun q.1).length = d - 1 :=
  factor_top_level_eq_depth_pred hn a B H happrox hd

end StrongTreeSpace
end Milliken
