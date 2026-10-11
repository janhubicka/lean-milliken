import Milliken.GeneralTree.BoundaryAncestor
import Milliken.AmbientChild
import Milliken.GeneralTree.ThinningStrong

/-!
# Every canonical boundary cone is occupied by a fixed-stem refinement

If S refines T and r_n(S)=r_n(T), the canonical ancestor map
from the n-th selected source level of S to that of T is
surjective.

For n=0 both source boundaries are root singletons. For n>0,
fix a boundary node q of T and find its predecessor p in the
common (n-1)-st source level. The unique S successor in the
ambient child cone from p to q has, by strongness of T, q as
its unique ancestor on T's n-th source level.

This proves that a strong refinement keeping the first n
source levels does not omit any of the finitely many
canonical boundary cones; no bounded global alphabet occurs.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Every T-boundary coordinate is attained by the canonical
ancestor of some S-node whenever S preserves the preceding
finite stem of T. -/
theorem boundaryAncestor_surjective_of_sameStem
    (S T : StrongSubtree U)
    (hST : S.Refines T) (n : ℕ)
    (hStem : r n S = r n T) :
    Function.Surjective (S.boundaryAncestor T hST n) := by
  classical
  cases n with
  | zero =>
      intro q
      let zS : SourceBoundary S 0 :=
        ⟨S.root, ⟨S.root_mem, S.root_level⟩⟩
      have hq : q.1 = T.root := by
        have h := q.2
        rw [T.sourceLevel_zero_eq_singleton] at h
        exact h
      have hmap : (S.boundaryAncestor T hST 0 zS).1 =
          T.root := by
        have h := (S.boundaryAncestor T hST 0 zS).2
        rw [T.sourceLevel_zero_eq_singleton] at h
        exact h
      exact ⟨zS, Subtype.ext (hmap.trans hq.symm)⟩
  | succ m =>
      intro q
      have hPrev : S.sourceLevel m = T.sourceLevel m := by
        calc
          S.sourceLevel m = maxLevel (r (m + 1) S) :=
            (maxLevel_r_succ S m).symm
          _ = maxLevel (r (m + 1) T) := by rw [hStem]
          _ = T.sourceLevel m := maxLevel_r_succ T m
      obtain ⟨p, hp, hpLevel, hpq⟩ :=
        T.predecessor_exists m q.1 q.2.1 q.2.2
      have hpS : p ∈ S.sourceLevel m := by
        rw [hPrev]
        exact ⟨hp, hpLevel⟩
      have hplt : p < q.1 := by
        rcases hpq.eq_or_lt with heq | hlt
        · have hh : U.level p = U.level q.1 :=
            congrArg (U.level) heq
          have hstrict :=
            T.levels_strictMono (Nat.lt_succ_self m)
          rw [hpLevel, q.2.2] at hh
          omega
        · exact hlt
      obtain ⟨y, hpy, hyq⟩ := U.exists_child_le_of_lt hplt
      obtain ⟨z, hz, _⟩ :=
        S.successor_unique m p hpS.1 hpS.2 y hpy
      let zS : SourceBoundary S (m + 1) :=
        ⟨z, ⟨hz.1, hz.2.1⟩⟩
      have hzT :
          z ∈ T.sourceLevel (S.refinementIndex T hST (m + 1)) :=
        S.sourceLevel_subset_refinementIndex T hST (m + 1)
          zS.2
      obtain ⟨q', hq', hq'z⟩ :=
        T.exists_sourceLevel_ancestor
          (S.le_refinementIndex T hST (m + 1)) hzT
      have hyrank : U.level y ≤ U.level q' := by
        have hstrict :=
          T.levels_strictMono (Nat.lt_succ_self m)
        calc
          U.level y = U.level p + 1 := U.level_covBy hpy
          _ = T.levels m + 1 := by rw [hpLevel]
          _ ≤ T.levels (m + 1) := by omega
          _ = U.level q' := hq'.2.symm
      have hyq' : y ≤ q' :=
        U.le_of_common_descendant_of_level_le
          hz.2.2 hq'z hyrank
      obtain ⟨w, hw, hunique⟩ :=
        T.successor_unique m p hp hpLevel y hpy
      have hqeq : q.1 = w :=
        hunique q.1 ⟨q.2.1, q.2.2, hyq⟩
      have hq'eq : q' = w :=
        hunique q' ⟨hq'.1, hq'.2, hyq'⟩
      have hqz : q.1 ≤ z := by
        calc
          q.1 = w := hqeq
          _ = q' := hq'eq.symm
          _ ≤ z := hq'z
      have hmaple :
          (S.boundaryAncestor T hST (m + 1) zS).1 ≤ z :=
        S.boundaryAncestor_le T hST (m + 1) zS
      have heq :
          (S.boundaryAncestor T hST (m + 1) zS).1 = q.1 :=
        U.eq_of_common_descendant_of_level_eq
          hmaple hqz
          ((S.boundaryAncestor T hST (m + 1) zS).2.2.trans
            q.2.2.symm)
      exact ⟨zS, Subtype.ext heq⟩

end StrongSubtree
end GeneralTree
end Milliken
