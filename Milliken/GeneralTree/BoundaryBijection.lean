import Milliken.GeneralTree.BoundarySurjective

/-!
# Bijection of canonical boundary cones under fixed-stem refinements

If S is a strong refinement of T preserving the first n selected
source levels, the canonical map from S's nth-level representatives
to their unique ancestors on T's nth level is not merely surjective:
it is injective.

Two S-representatives sharing a T-boundary ancestor would lie
above the same immediate ambient child cone of a node on the
common previous selected level, contradicting S's successor
uniqueness. The source-zero case is the singleton root case.

Together with the verified surjectivity lemma this gives the
precise finite coordinate correspondence used to encode
one-step extensions in the A.4 Halpern–Läuchli product.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Two nth-level selected nodes of S cannot descend from
the same nth-level T node when their initial height-n
finite stems are equal. -/
theorem eq_of_same_boundary_ancestor
    (S T : StrongSubtree U) (n : ℕ)
    (hStem : r n S = r n T)
    {z w q : U}
    (hz : z ∈ S.sourceLevel n)
    (hw : w ∈ S.sourceLevel n)
    (hq : q ∈ T.sourceLevel n)
    (hqz : q ≤ z) (hqw : q ≤ w) :
    z = w := by
  cases n with
  | zero =>
      have hzroot : z = S.root := by
        have h := hz
        rw [S.sourceLevel_zero_eq_singleton] at h
        exact h
      have hwroot : w = S.root := by
        have h := hw
        rw [S.sourceLevel_zero_eq_singleton] at h
        exact h
      exact hzroot.trans hwroot.symm
  | succ m =>
      have hPrev : S.sourceLevel m = T.sourceLevel m := by
        calc
          S.sourceLevel m = maxLevel (r (m + 1) S) :=
            (maxLevel_r_succ S m).symm
          _ = maxLevel (r (m + 1) T) := by rw [hStem]
          _ = T.sourceLevel m := maxLevel_r_succ T m
      obtain ⟨p, hp, hpLevel, hpq⟩ :=
        T.predecessor_exists m q hq.1 hq.2
      have hpS : p ∈ S.sourceLevel m := by
        rw [hPrev]
        exact ⟨hp, hpLevel⟩
      have hpLt : p < q := by
        rcases hpq.eq_or_lt with heq | hlt
        · have hh : U.level p = U.level q :=
            congrArg (U.level) heq
          have hstrict :=
            T.levels_strictMono (show m < m + 1 by omega)
          rw [hpLevel, hq.2] at hh
          omega
        · exact hlt
      obtain ⟨y, hpy, hyq⟩ := U.exists_child_le_of_lt hpLt
      obtain ⟨u, hu, hunique⟩ :=
        S.successor_unique m p hpS.1 hpS.2 y hpy
      have hzu : z = u :=
        hunique z ⟨hz.1, hz.2, hyq.trans hqz⟩
      have hwu : w = u :=
        hunique w ⟨hw.1, hw.2, hyq.trans hqw⟩
      exact hzu.trans hwu.symm

/-- The unique T-boundary ancestor map is injective when S
preserves the first n selected levels of T. -/
theorem boundaryAncestor_injective_of_sameStem
    (S T : StrongSubtree U)
    (hST : S.Refines T) (n : ℕ)
    (hStem : r n S = r n T) :
    Function.Injective (S.boundaryAncestor T hST n) := by
  intro z w hzw
  apply Subtype.ext
  let q : SourceBoundary T n :=
    S.boundaryAncestor T hST n z
  have hqz : q.1 ≤ z.1 :=
    S.boundaryAncestor_le T hST n z
  have hqw : q.1 ≤ w.1 := by
    change (S.boundaryAncestor T hST n z).1 ≤ w.1
    rw [hzw]
    exact S.boundaryAncestor_le T hST n w
  exact S.eq_of_same_boundary_ancestor T n hStem
    z.2 w.2 q.2 hqz hqw

/-- The exact finite boundary-coordinate bijection of any
stem-preserving strong refinement with its containing tree. -/
theorem boundaryAncestor_bijective_of_sameStem
    (S T : StrongSubtree U)
    (hST : S.Refines T) (n : ℕ)
    (hStem : r n S = r n T) :
    Function.Bijective (S.boundaryAncestor T hST n) := by
  exact ⟨S.boundaryAncestor_injective_of_sameStem T hST n hStem,
    S.boundaryAncestor_surjective_of_sameStem T hST n hStem⟩

end StrongSubtree
end GeneralTree
end Milliken
