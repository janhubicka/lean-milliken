import Milliken.GeneralTree.LowerFinite

/-!
# A.2(2): published finitisation realises arbitrary-tree refinement

Strong subtree inclusion can be recovered precisely from containment
of arbitrarily long finite approximations in the *published* order
(6.3), using both carrier inclusion and maximal-level inclusion.

For the forward direction, a selected level of S below T must align
with a selected level of T; all earlier source levels then lie in the
corresponding finite prefix of T. For the reverse direction, any node
of S belongs to some finite prefix, which is contained in a finite
prefix of T.

This uses no global bound on the local finite branching degrees.
A.2(3) prefix compatibility remains to be checked separately.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- Selected ambient heights of a strong refinement are selected heights
of the larger strong subtree. -/
theorem selectedLevel_of_refines
    {S T : StrongSubtree U} (hST : S.Refines T) (n : ℕ) :
    ∃ m : ℕ, S.levels n = T.levels m := by
  obtain ⟨x, hx⟩ := S.sourceLevel_nonempty n
  obtain ⟨m, hm⟩ := T.carrier_levels x (hST hx.1)
  exact ⟨m, hx.2.symm.trans hm⟩

/-- A node of T whose ambient height is at most T's jth selected
height belongs to T's first j+1 source levels. -/
theorem mem_initialPart_of_level_le
    (T : StrongSubtree U) (j : ℕ)
    {x : U} (hx : x ∈ T.carrier)
    (hle : U.level x ≤ T.levels j) :
    x ∈ T.initialPart (j + 1) := by
  obtain ⟨k, hk⟩ := T.carrier_levels x hx
  have hkj : k ≤ j := by
    by_contra hnot
    have hjk : j < k := Nat.lt_of_not_ge hnot
    have hstrict := T.levels_strictMono hjk
    omega
  exact ⟨hx, k, Nat.lt_succ_of_le hkj, hk⟩

end StrongSubtree

/-- Strong refinement produces the published finite-order witness
for every finite source height (A.2 forward direction). -/
theorem exists_bookLeFin_r_of_refines
    (S T : SInfinity U) (hST : S.Refines T) (n : ℕ) :
    ∃ m : ℕ, bookLeFin
      ⟨n, r n S⟩ ⟨m, r m T⟩ := by
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      exact bookLeFin_zero_left S ⟨0, r 0 T⟩
  | succ n =>
      obtain ⟨j, hlevel⟩ := S.selectedLevel_of_refines hST n
      refine ⟨j + 1, bookLeFin_iff.mpr ?_⟩
      constructor
      · change S.initialPart (n + 1) ⊆
          T.initialPart (j + 1)
        rintro x ⟨hx, k, hk, hklevel⟩
        have hkn : k ≤ n := Nat.le_of_lt_succ hk
        have hxlevel : U.level x ≤ T.levels j := by
          calc
            U.level x = S.levels k := hklevel
            _ ≤ S.levels n := S.levels_strictMono.monotone hkn
            _ = T.levels j := hlevel
        exact T.mem_initialPart_of_level_le j (hST hx) hxlevel
      · change maxLevel (r (n + 1) S) ⊆
          maxLevel (r (j + 1) T)
        rw [maxLevel_r_succ S n, maxLevel_r_succ T j]
        rintro x ⟨hx, hxlevel⟩
        exact ⟨hST hx, hxlevel.trans hlevel⟩

/-- If every finite approximation of S is below a finite
approximation of T in (6.3), then S is a strong refinement of T. -/
theorem refines_of_forall_bookLeFin_r
    (S T : SInfinity U)
    (h : ∀ n : ℕ,
      ∃ m : ℕ, bookLeFin ⟨n, r n S⟩ ⟨m, r m T⟩) :
    S.Refines T := by
  intro x hx
  obtain ⟨n, hn⟩ := S.carrier_levels x hx
  obtain ⟨m, hm⟩ := h (n + 1)
  have hmem : x ∈ (r (n + 1) S).carrier :=
    ⟨hx, n, Nat.lt_succ_self n, hn⟩
  have hmemT : x ∈ (r m T).carrier :=
    (bookLeFin_iff.mp hm).1 hmem
  exact T.initialPart_subset m hmemT

/-- The published order (6.3) realizes the infinite strong-subtree
refinement quasi-order: Todorčević A.2(2), for any ambient U. -/
theorem refines_iff_forall_bookLeFin_r
    (S T : SInfinity U) :
    S.Refines T ↔
      ∀ n : ℕ,
        ∃ m : ℕ, bookLeFin ⟨n, r n S⟩ ⟨m, r m T⟩ := by
  constructor
  · intro hST n
    exact exists_bookLeFin_r_of_refines S T hST n
  · exact refines_of_forall_bookLeFin_r S T

end GeneralTree
end Milliken
