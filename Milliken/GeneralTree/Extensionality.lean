import Milliken.GeneralTree.OrderLemmas

/-!
# A.1 separation for arbitrary rooted finitely branching strong trees

An infinite strong subtree is represented by its carrier, selected level
map and a root. The latter two pieces of data are *determined* by the
carrier: a strictly increasing sequence has a unique enumeration of
its range, while the selected root is the least node of the carrier.

Consequently equality of all finite approximations is enough to conclude
equality of the original infinite strong subtrees. No globally fixed
branching degree or alphabet is needed.
-/

namespace Milliken
namespace GeneralTree

/-- Two strictly increasing sequences of naturals with the same range
are the same sequence. -/
theorem strictMono_eq_of_range_eq {f g : ℕ → ℕ}
    (hf : StrictMono f) (hg : StrictMono g)
    (hfg : Set.range f = Set.range g) :
    f = g := by
  funext n
  induction n with
  | zero =>
      have hgmem : g 0 ∈ Set.range f := by
        rw [hfg]
        exact ⟨0, rfl⟩
      obtain ⟨i, hi⟩ := hgmem
      have hfmem : f 0 ∈ Set.range g := by
        rw [← hfg]
        exact ⟨0, rfl⟩
      obtain ⟨j, hj⟩ := hfmem
      apply le_antisymm
      · calc
          f 0 ≤ f i := hf.monotone (Nat.zero_le i)
          _ = g 0 := hi
      · calc
          g 0 ≤ g j := hg.monotone (Nat.zero_le j)
          _ = f 0 := hj
  | succ n ih =>
      apply le_antisymm
      · by_contra hn
        have hlt : g (n + 1) < f (n + 1) := lt_of_not_ge hn
        have hgmem : g (n + 1) ∈ Set.range f := by
          rw [hfg]
          exact ⟨n + 1, rfl⟩
        obtain ⟨k, hk⟩ := hgmem
        have hnk : n < k := (hf.lt_iff_lt).mp (by
          calc
            f n = g n := ih
            _ < g (n + 1) := hg (Nat.lt_succ_self n)
            _ = f k := hk.symm)
        have hks : k < n + 1 := (hf.lt_iff_lt).mp (by
          calc
            f k = g (n + 1) := hk
            _ < f (n + 1) := hlt)
        omega
      · by_contra hn
        have hlt : f (n + 1) < g (n + 1) := lt_of_not_ge hn
        have hfmem : f (n + 1) ∈ Set.range g := by
          rw [← hfg]
          exact ⟨n + 1, rfl⟩
        obtain ⟨k, hk⟩ := hfmem
        have hnk : n < k := (hg.lt_iff_lt).mp (by
          calc
            g n = f n := ih.symm
            _ < f (n + 1) := hf (Nat.lt_succ_self n)
            _ = g k := hk.symm)
        have hks : k < n + 1 := (hg.lt_iff_lt).mp (by
          calc
            g k = f (n + 1) := hk
            _ < g (n + 1) := hlt)
        omega

namespace StrongSubtree

variable {U : AmbientTree}

/-- The set of selected ambient levels is exactly the set of ambient
ranks attained on the carrier. -/
theorem range_levels_eq_carrier_ranks (S : StrongSubtree U) :
    Set.range S.levels =
      {n | ∃ x ∈ S.carrier, U.level x = n} := by
  ext n
  constructor
  · rintro ⟨k, rfl⟩
    obtain ⟨x, hx⟩ := S.sourceLevel_nonempty k
    exact ⟨x, hx.1, hx.2⟩
  · rintro ⟨x, hx, hn⟩
    obtain ⟨k, hk⟩ := S.carrier_levels x hx
    exact ⟨k, hk.symm.trans hn⟩

/-- All strong-subtree structure data is determined by its node carrier.
This source-facing extensionality lemma is needed for A.1 separation. -/
@[ext] theorem ext_carrier {S T : StrongSubtree U}
    (h : S.carrier = T.carrier) : S = T := by
  have hrange : Set.range S.levels = Set.range T.levels := by
    rw [S.range_levels_eq_carrier_ranks, T.range_levels_eq_carrier_ranks, h]
  have hlevels : S.levels = T.levels :=
    strictMono_eq_of_range_eq S.levels_strictMono
      T.levels_strictMono hrange
  have hroot : S.root = T.root := by
    apply le_antisymm
    · apply S.root_below
      rw [h]
      exact T.root_mem
    · apply T.root_below
      rw [← h]
      exact S.root_mem
  cases S with
  | mk cS lS hmonoS rootS hrootS hlS rbS clS peS suS =>
    cases T with
    | mk cT lT hmonoT rootT hrootT hlT rbT clT peT suT =>
      dsimp at h hlevels hroot
      cases h
      cases hlevels
      cases hroot
      rfl

end StrongSubtree

/-- A.1 separation: knowing every finite source-level approximation
determines an arbitrary infinite strong subtree. -/
theorem r_separated {U : AmbientTree} {S T : SInfinity U}
    (h : ∀ n : ℕ, r n S = r n T) : S = T := by
  apply StrongSubtree.ext_carrier
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := S.carrier_levels x hx
    have hin : x ∈ S.initialPart (n + 1) :=
      ⟨hx, n, Nat.lt_succ_self n, hn⟩
    have hpart : S.initialPart (n + 1) = T.initialPart (n + 1) :=
      congrArg FiniteApprox.carrier (h (n + 1))
    rw [hpart] at hin
    exact (T.initialPart_subset (n + 1)) hin
  · intro hx
    obtain ⟨n, hn⟩ := T.carrier_levels x hx
    have hin : x ∈ T.initialPart (n + 1) :=
      ⟨hx, n, Nat.lt_succ_self n, hn⟩
    have hpart : S.initialPart (n + 1) = T.initialPart (n + 1) :=
      congrArg FiniteApprox.carrier (h (n + 1))
    rw [← hpart] at hin
    exact (S.initialPart_subset (n + 1)) hin

end GeneralTree
end Milliken
