import Milliken.GeneralTree.Published

/-!
# Basic laws of selected source levels

The definitions are those of Todorčević, Chapter 6: source levels of a
strong subtree can skip ambient levels and the first n source levels
form the approximation r_n. These results use only (str1) and do not
assume a common branching alphabet or a global degree bound.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Selected source levels belong to the underlying strong tree. -/
theorem sourceLevel_subset_carrier (S : StrongSubtree U) (n : ℕ) :
    S.sourceLevel n ⊆ S.carrier :=
  fun _ hx => hx.1

/-- Level n is contained in the initial part of any larger source height. -/
theorem sourceLevel_subset_initialPart
    (S : StrongSubtree U) {n m : ℕ} (hnm : n < m) :
    S.sourceLevel n ⊆ S.initialPart m := by
  rintro x ⟨hx, hlevel⟩
  exact ⟨hx, n, hnm, hlevel⟩

/-- The next approximation adds exactly one selected source level. -/
theorem initialPart_succ (S : StrongSubtree U) (n : ℕ) :
    S.initialPart (n + 1) =
      S.initialPart n ∪ S.sourceLevel n := by
  ext x
  constructor
  · rintro ⟨hx, k, hk, hlevel⟩
    rcases (Nat.lt_succ_iff_lt_or_eq.mp hk) with hkn | hkn
    · exact Or.inl ⟨hx, k, hkn, hlevel⟩
    · subst k
      exact Or.inr ⟨hx, hlevel⟩
  · intro hx
    rcases hx with ⟨hx, k, hkn, hlevel⟩ | ⟨hx, hlevel⟩
    · exact ⟨hx, k, Nat.lt_succ_of_lt hkn, hlevel⟩
    · exact ⟨hx, n, Nat.lt_succ_self n, hlevel⟩

/-- The tree is the union of all its selected source levels. -/
theorem carrier_eq_iUnion_sourceLevel (S : StrongSubtree U) :
    S.carrier = ⋃ n : ℕ, S.sourceLevel n := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := S.carrier_levels x hx
    exact Set.mem_iUnion.mpr ⟨n, hx, hn⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
    exact hn.1

/-- Distinct selected source levels are disjoint. -/
theorem sourceLevel_disjoint (S : StrongSubtree U)
    {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (S.sourceLevel n) (S.sourceLevel m) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hlevels : S.levels n = S.levels m :=
    hx.2.symm.trans hy.2
  exact hnm (S.levels_strictMono.injective hlevels)

end StrongSubtree
end GeneralTree
end Milliken
