import Milliken.GeneralTree.MaxLevel

/-!
# A.1 coherence for arbitrary pruned finitely branching ambient trees

The carrier of the previous finite approximation is the carrier of
the successor approximation with its maximal selected source level
removed. This reconstruction is intrinsic to the induced finite tree:
it does not depend on choosing a realization.

Thus equality of two height-n approximations forces equality at
every preceding source height. No global degree bound is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- The preceding finite stem is the successor stem minus its
maximal selected source level. -/
theorem initialPart_eq_diff (S : StrongSubtree U) (n : ℕ) :
    S.initialPart n =
      S.initialPart (n + 1) \ S.sourceLevel n := by
  ext x
  constructor
  · intro hx
    refine ⟨S.initialPart_mono (Nat.le_succ n) hx, ?_⟩
    intro hxTop
    obtain ⟨_, k, hk, hlevel⟩ := hx
    have hlt : S.levels k < S.levels n :=
      S.levels_strictMono hk
    exact (Nat.ne_of_lt hlt) (hlevel.symm.trans hxTop.2)
  · intro hx
    have hpart :
        S.initialPart (n + 1) =
          S.initialPart n ∪ S.sourceLevel n :=
      S.initialPart_succ n
    have hmem : x ∈ S.initialPart n ∪ S.sourceLevel n := by
      rw [← hpart]
      exact hx.1
    rcases hmem with hprev | htop
    · exact hprev
    · exact (hx.2 htop).elim

end StrongSubtree

/-- Equality of height-(n+1) approximations determines their
height-n truncations: the maximal levels agree by (6.3). -/
theorem r_prev_eq_of_succ
    {S T : SInfinity U} {n : ℕ}
    (h : r (n + 1) S = r (n + 1) T) :
    r n S = r n T := by
  have hcar : S.initialPart (n + 1) =
      T.initialPart (n + 1) :=
    congrArg FiniteApprox.carrier h
  have htop : S.sourceLevel n = T.sourceLevel n := by
    calc
      S.sourceLevel n = maxLevel (r (n + 1) S) :=
        (maxLevel_r_succ S n).symm
      _ = maxLevel (r (n + 1) T) := by rw [h]
      _ = T.sourceLevel n := maxLevel_r_succ T n
  apply FiniteApprox.ext_carrier
  change S.initialPart n = T.initialPart n
  rw [S.initialPart_eq_diff n, T.initialPart_eq_diff n,
      hcar, htop]

/-- A.1 coherence: agreement at one finite selected-source height
implies agreement at every lower selected-source height. -/
theorem r_coherent_le (S T : SInfinity U) :
    ∀ n, r n S = r n T →
      ∀ m, m ≤ n → r m S = r m T := by
  intro n
  induction n with
  | zero =>
      intro h m hm
      have hzero : m = 0 := by omega
      subst m
      exact r_zero_eq S T
  | succ n ih =>
      intro h m hm
      by_cases heq : m = n + 1
      · subst m
        exact h
      · exact ih (r_prev_eq_of_succ h) m (by omega)

end GeneralTree
end Milliken
