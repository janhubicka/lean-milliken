import Milliken.GeneralTree.FiniteLevels

/-!
# Todorčević (6.3): the maximal level of a finite strong subtree

The printed order uses `a(max)`, the maximal nodes of the *finite induced
tree*. It is critical not to replace this by the whole carrier or by the
last ambient level unconditionally.

For a realized finite strong subtree of height `n + 1`, the maximal
nodes are exactly the `n`th selected source level of its realizer.
The proof uses the ambient rank order, prunedness, and the exact
ambient-successor extension clause (str2), without a fixed alphabet.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- The maximal nodes of the first `n+1` selected source levels are
exactly the final selected source level. This identifies the
book's `a(max)` with an explicit level set. -/
theorem maxLevel_r_succ (S : StrongSubtree U) (n : ℕ) :
    maxLevel (r (n + 1) S) = S.sourceLevel n := by
  ext x
  change
    (x ∈ S.initialPart (n + 1) ∧
      ∀ y ∈ S.initialPart (n + 1), x ≤ y → y = x) ↔
    x ∈ S.sourceLevel n
  constructor
  · rintro ⟨⟨hx, k, hkn, hlevel⟩, hmax⟩
    have hk_le : k ≤ n := Nat.le_of_lt_succ hkn
    have hk_eq : k = n := by
      by_contra hneq
      have hk_lt : k < n := lt_of_le_of_ne hk_le hneq
      obtain ⟨y, hxy⟩ := U.has_child x
      obtain ⟨z, hz, _⟩ :=
        S.successor_unique k x hx hlevel y hxy
      have hzPart : z ∈ S.initialPart (n + 1) := by
        refine ⟨hz.1, k + 1, ?_, hz.2.1⟩
        omega
      have hxz : x ≤ z := hxy.le.trans hz.2.2
      have hxz_strict : x < z := hxy.lt.trans_le hz.2.2
      have hzx : z = x := hmax z hzPart hxz
      exact (ne_of_gt hxz_strict) hzx
    exact ⟨hx, hk_eq ▸ hlevel⟩
  · rintro ⟨hx, hlevel⟩
    refine ⟨⟨hx, n, Nat.lt_succ_self n, hlevel⟩, ?_⟩
    intro y hy hxy
    obtain ⟨hyS, k, hkn, hyLevel⟩ := hy
    have hrank : S.levels n ≤ S.levels k := by
      calc
        S.levels n = U.level x := hlevel.symm
        _ ≤ U.level y := U.level_mono hxy
        _ = S.levels k := hyLevel
    have hnk : n ≤ k := by
      by_contra hnot
      have hkn_lt : k < n := Nat.lt_of_not_ge hnot
      have hreverse := S.levels_strictMono hkn_lt
      omega
    have hkle : k ≤ n := Nat.le_of_lt_succ hkn
    have hkeq : k = n := le_antisymm hkle hnk
    have hsame : U.level x = U.level y := by
      calc
        U.level x = S.levels n := hlevel
        _ = S.levels k := by rw [hkeq]
        _ = U.level y := hyLevel.symm
    exact (U.eq_of_le_of_level_eq hxy hsame).symm

/-- The maximal level of the empty approximation is empty. -/
@[simp] theorem maxLevel_r_zero (S : StrongSubtree U) :
    maxLevel (r 0 S) = ∅ := by
  ext x
  constructor
  · intro hx
    have hcar : x ∈ (r 0 S).carrier :=
      (maxLevel_subset_carrier (r 0 S)) hx
    rw [r_zero_carrier] at hcar
    simp at hcar
  · simp

end GeneralTree
end Milliken
