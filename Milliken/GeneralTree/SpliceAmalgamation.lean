import Milliken.GeneralTree.StrongGraft
import RamseySpace.Axioms

/-!
# Positive-height A.3(1) from the arbitrary-tree graft

The root/frontier graft preserves the initial finite strong tree
through its last selected source level, including the height-one
case. The published depth (using maximal-level inclusion) aligns
that frontier with the final selected level of the prescribed
initial approximation of B. A depth-preserving refinement A has
the same selected frontier nodes, and thus supports an actual
strong graft realizing the prescribed finite stem.

This proves Todorčević A.3(1) for all arbitrary pruned locally
finite ambient trees, with no uniform branching-degree bound.
A.3(2) remains the separate protected-splice construction.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- The splice preserves each selected source level strictly
before its cut. -/
theorem spliceStrong_sourceLevel_before
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j)
    {k : ℕ} (hk : k < n) :
    (S.spliceStrong T n j htop).sourceLevel k =
      S.sourceLevel k := by
  change
    {z : U | z ∈ S.spliceCarrier T n ∧
      U.level z = S.spliceLevels T n j k} =
      S.sourceLevel k
  rw [S.spliceLevels_before T hk]
  exact S.spliceCarrier_level_before T hk

/-- The first tail level of the genuine graft is precisely
the old selected frontier. -/
theorem spliceStrong_sourceLevel_at
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    (S.spliceStrong T n j htop).sourceLevel n =
      S.sourceLevel n := by
  have hlevel : S.levels n = T.levels j := by
    obtain ⟨x, hx⟩ := S.sourceLevel_nonempty n
    exact hx.2.symm.trans (htop hx).2
  have hAt :
      S.spliceLevels T n j n = S.levels n := by
    calc
      S.spliceLevels T n j n = T.levels j := by
        simpa only [Nat.add_zero] using
          (S.spliceLevels_at T n j 0)
      _ = S.levels n := hlevel.symm
  change
    {z : U | z ∈ S.spliceCarrier T n ∧
      U.level z = S.spliceLevels T n j n} =
      S.sourceLevel n
  rw [hAt]
  exact S.spliceCarrier_level_at T n (fun x hx => (htop hx).1)

/-- The graft agrees with S on its first n selected source
levels, without requiring n positive. -/
theorem spliceStrong_initialPart
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    (S.spliceStrong T n j htop).initialPart n =
      S.initialPart n := by
  let C := S.spliceStrong T n j htop
  ext z
  constructor
  · rintro ⟨hz, k, hk, hlevel⟩
    have hzk : z ∈ C.sourceLevel k := ⟨hz, hlevel⟩
    have hsource : C.sourceLevel k = S.sourceLevel k :=
      S.spliceStrong_sourceLevel_before T n j htop hk
    rw [hsource] at hzk
    exact ⟨hzk.1, k, hk, hzk.2⟩
  · rintro ⟨hz, k, hk, hlevel⟩
    have hzk : z ∈ S.sourceLevel k := ⟨hz, hlevel⟩
    have hsource : C.sourceLevel k = S.sourceLevel k :=
      S.spliceStrong_sourceLevel_before T n j htop hk
    rw [← hsource] at hzk
    exact ⟨hzk.1, k, hk, hzk.2⟩

/-- The positive-height finite approximation of the graft
is exactly the original finite strong stem. -/
theorem spliceStrong_initialPart_succ
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    (S.spliceStrong T n j htop).initialPart (n + 1) =
      S.initialPart (n + 1) := by
  let C := S.spliceStrong T n j htop
  calc
    C.initialPart (n + 1) =
        C.initialPart n ∪ C.sourceLevel n :=
      C.initialPart_succ n
    _ = S.initialPart n ∪ S.sourceLevel n := by
      rw [S.spliceStrong_initialPart T n j htop,
        S.spliceStrong_sourceLevel_at T n j htop]
    _ = S.initialPart (n + 1) :=
      (S.initialPart_succ n).symm

/-- Exact finite-approximation identity for the strong graft. -/
theorem spliceStrong_approx_succ
    (S T : StrongSubtree U)
    (n j : ℕ)
    (htop : S.sourceLevel n ⊆ T.sourceLevel j) :
    r (n + 1) (S.spliceStrong T n j htop) =
      r (n + 1) S := by
  apply FiniteApprox.ext_carrier
  exact S.spliceStrong_initialPart_succ T n j htop

end StrongSubtree

/-- Todorčević A.3(1): any depth-preserving strong-tree
refinement admits a realization of the prescribed finite stem,
for arbitrary pruned locally finitely branching ambient U. -/
theorem generalAmalgamation_nonempty
    {n : ℕ} (a : (generalApproximationSystem U).Approx n)
    (B : (generalApproximationSystem U).Point) {d : ℕ}
    (hd : (generalBookFinitization U).HasDepth a B d) :
    ∀ ⦃A : (generalApproximationSystem U).Point⦄,
      A ∈ (generalApproximationSystem U).levelNeighborhood d B →
        ((generalApproximationSystem U).neighborhood a A).Nonempty := by
  intro A hA
  cases n with
  | zero =>
      exact neighborhood_nonempty_zero a A
  | succ n =>
      obtain ⟨S, hSa⟩ := a.realised
      have haS : r (n + 1) S = a := by
        apply FiniteApprox.ext_carrier
        exact hSa.symm
      obtain ⟨j, hdEq, htopa⟩ :=
        bookDepth_succ_lastLevel a B hd
      have htopB : S.sourceLevel n ⊆ B.sourceLevel j := by
        have hmax : S.sourceLevel n = maxLevel a := by
          calc
            S.sourceLevel n = maxLevel (r (n + 1) S) :=
              (maxLevel_r_succ S n).symm
            _ = maxLevel a := by rw [haS]
        rw [hmax]
        exact htopa
      have hAB : r (j + 1) A = r (j + 1) B := by
        have h := hA.2
        change r d A = r d B at h
        rw [hdEq] at h
        exact h
      have htopEq : A.sourceLevel j = B.sourceLevel j := by
        calc
          A.sourceLevel j = maxLevel (r (j + 1) A) :=
            (maxLevel_r_succ A j).symm
          _ = maxLevel (r (j + 1) B) := by rw [hAB]
          _ = B.sourceLevel j := maxLevel_r_succ B j
      have htopA : S.sourceLevel n ⊆ A.sourceLevel j := by
        rw [htopEq]
        exact htopB
      have hcarA : a.carrier ⊆ A.carrier := by
        have hcarB : a.carrier ⊆ (r d B).carrier :=
          (bookLeFin_iff.mp hd.1).1
        intro z hz
        have hzA : z ∈ (r d A).carrier := by
          have hAB' : r d A = r d B := hA.2
          rw [hAB']
          exact hcarB hz
        exact A.initialPart_subset d hzA
      have hprefix : S.initialPart n ⊆ A.carrier := by
        intro z hz
        apply hcarA
        rw [hSa]
        exact S.initialPart_mono (Nat.le_succ n) hz
      let C := S.spliceStrong A n j htopA
      have hCA : C.Refines A :=
        S.spliceStrong_refines A n j htopA hprefix
      have hCa : r (n + 1) C = a :=
        (S.spliceStrong_approx_succ A n j htopA).trans haS
      exact ⟨C, hCA, hCa⟩

end GeneralTree
end Milliken
