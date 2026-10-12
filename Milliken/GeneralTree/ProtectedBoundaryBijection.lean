import Milliken.GeneralTree.ProtectedBoundaryLift
import Milliken.GeneralTree.RefinementLevels
import Milliken.GeneralTree.BoundaryCones

/-!
# Exact boundary correspondence through protected strong refinements

If T strongly refines S and their finite approximations of height n
agree, every node of the S source-n frontier has exactly one
descendant in the T source-n frontier. Conversely every node of the
new frontier descends from a unique old source-n frontier node.

Consequently the descendant relation defines an equivalence of the
actual finite source-n boundary index types. This does not assume
a fixed alphabet, globally bounded branching, or any Ramsey theorem.

The bijection is the bookkeeping device needed to turn local
cone constancy into a statement about all boundary tuples at
each finite heterogeneous stabilization stage.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The earlier existence of a lifted boundary point is unique:
the protected source-(n-1) frontier fixes its predecessor, and
the strong-successor condition chooses exactly one descendant
of each actual immediate child cone. -/
theorem existsUnique_sourceLevel_lift_of_refines
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S)
    {x : U} (hx : x ∈ S.sourceLevel n) :
    ∃! y : U, y ∈ T.sourceLevel n ∧ x ≤ y := by
  obtain ⟨y, hy, hxy⟩ :=
    S.exists_sourceLevel_lift_of_refines T hTS happrox hx
  refine ⟨y, ⟨hy, hxy⟩, ?_⟩
  intro z hz
  cases n with
  | zero =>
      have hzroot : z = T.root := by
        simpa only [T.sourceLevel_zero_eq_singleton,
          Set.mem_singleton_iff] using hz.1
      have hyroot : y = T.root := by
        simpa only [T.sourceLevel_zero_eq_singleton,
          Set.mem_singleton_iff] using hy
      exact hzroot.trans hyroot.symm
  | succ m =>
      have htop : T.sourceLevel m = S.sourceLevel m := by
        calc
          T.sourceLevel m = maxLevel (r (m + 1) T) :=
            (maxLevel_r_succ T m).symm
          _ = maxLevel (r (m + 1) S) := by rw [happrox]
          _ = S.sourceLevel m := maxLevel_r_succ S m
      obtain ⟨p, hp, hpLevel, hpx⟩ :=
        S.predecessor_exists m x hx.1 hx.2
      have hpT : p ∈ T.sourceLevel m := by
        rw [htop]
        exact ⟨hp, hpLevel⟩
      have hpxlt : p < x := by
        rcases hpx.eq_or_lt with heq | hlt
        · have hlevel : S.levels m = S.levels (m + 1) := by
            calc
              S.levels m = U.level p := hpLevel.symm
              _ = U.level x := congrArg U.level heq
              _ = S.levels (m + 1) := hx.2
          have hstrict : S.levels m < S.levels (m + 1) :=
            S.levels_strictMono (Nat.lt_succ_self m)
          omega
        · exact hlt
      obtain ⟨c, hpc, hcx⟩ :=
        U.exists_child_le_of_lt hpxlt
      obtain ⟨w, hw, hunique⟩ :=
        T.successor_unique m p hpT.1 hpT.2 c hpc
      have hzy : z = w :=
        hunique z ⟨hz.1.1, hz.1.2, hcx.trans hz.2⟩
      have hyw : y = w :=
        hunique y ⟨hy.1, hy.2, hcx.trans hxy⟩
      exact hzy.trans hyw.symm

/-- The actual descendant of a protected source-n boundary node. -/
noncomputable def protectedBoundaryLift
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S) :
    SourceBoundary S n → SourceBoundary T n := by
  classical
  intro x
  let witness :=
    S.existsUnique_sourceLevel_lift_of_refines
      T hTS happrox x.2
  exact ⟨Classical.choose witness,
    (Classical.choose_spec witness).1.1⟩

theorem protectedBoundaryLift_above
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S)
    (x : SourceBoundary S n) :
    x.1 ≤ (S.protectedBoundaryLift T hTS happrox x).1 := by
  classical
  exact (Classical.choose_spec
    (S.existsUnique_sourceLevel_lift_of_refines
      T hTS happrox x.2)).1.2

/-- Distinct old boundary nodes cannot share a lifted node,
because they have the same old selected ambient rank. -/
theorem protectedBoundaryLift_injective
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S) :
    Function.Injective (S.protectedBoundaryLift T hTS happrox) := by
  intro x y hxy
  apply Subtype.ext
  have hx := S.protectedBoundaryLift_above T hTS happrox x
  have hy := S.protectedBoundaryLift_above T hTS happrox y
  rw [← hxy] at hy
  have heq : U.level x.1 = U.level y.1 :=
    x.2.2.trans y.2.2.symm
  rcases le_total_of_directed hx hy with hyx | hxy
  · exact (U.eq_of_le_of_level_eq hyx heq.symm).symm
  · exact U.eq_of_le_of_level_eq hxy heq

/-- Every new boundary node descends from one old node on the
same source frontier and therefore is in the image of the lift. -/
theorem protectedBoundaryLift_surjective
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S) :
    Function.Surjective (S.protectedBoundaryLift T hTS happrox) := by
  intro y
  have hn :
      n ≤ T.refinementIndex S hTS n :=
    T.le_refinementIndex S hTS n
  have hyS :
      y.1 ∈ S.sourceLevel (T.refinementIndex S hTS n) :=
    T.sourceLevel_subset_refinementIndex S hTS n y.2
  obtain ⟨x, hx, hxy⟩ :=
    S.exists_sourceLevel_ancestor hn hyS
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  change
    Classical.choose
      (S.existsUnique_sourceLevel_lift_of_refines
        T hTS happrox hx) = y.1
  exact ((Classical.choose_spec
    (S.existsUnique_sourceLevel_lift_of_refines
      T hTS happrox hx)).2 y.1 ⟨y.2, hxy⟩).symm

/-- The protected boundary is mapped bijectively to the new
boundary by the unique source-level-descendant relation. -/
noncomputable def protectedBoundaryEquiv
    (S T : StrongSubtree U) {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S) :
    SourceBoundary S n ≃ SourceBoundary T n :=
  Equiv.ofBijective
    (S.protectedBoundaryLift T hTS happrox)
    ⟨S.protectedBoundaryLift_injective T hTS happrox,
      S.protectedBoundaryLift_surjective T hTS happrox⟩

end StrongSubtree
end GeneralTree
end Milliken
