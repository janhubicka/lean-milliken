import Milliken.GeneralTree.HeterogeneousTruncation
import Milliken.AmbientChild

/-!
# Lifting every old boundary node through a protected strong refinement

For a strong refinement T of S preserving the first n selected
source levels, every S-node on its nth source level has a T-node
on the new nth source level above it.

The positive-height proof uses the common top frontier at n-1,
the actual ambient immediate-child cone leading to the old node,
the unique next T-successor in that cone, and the unique S-ancestor
of this successor on its former nth selected source level.

The result lifts whole finite product boundary tuples through
coordinatewise protected strong refinements, with no synchronized
ambient level assumption or branching bound. This is the finite
fusion geometry needed to preserve earlier stabilization requirements.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

/-- A refinement preserving the first n selected levels has a
source-n descendant above every original source-n node. -/
theorem exists_sourceLevel_lift_of_refines
    (S T : StrongSubtree U)
    {n : ℕ}
    (hTS : T.Refines S)
    (happrox : r n T = r n S)
    {x : U}
    (hx : x ∈ S.sourceLevel n) :
    ∃ y : U, y ∈ T.sourceLevel n ∧ x ≤ y := by
  cases n with
  | zero =>
      have hroot : x = S.root := by
        simpa only [S.sourceLevel_zero_eq_singleton,
          Set.mem_singleton_iff] using hx
      refine ⟨T.root, ⟨T.root_mem, T.root_level⟩, ?_⟩
      rw [hroot]
      exact S.root_below T.root (hTS T.root_mem)
  | succ m =>
      have htop : T.sourceLevel m = S.sourceLevel m := by
        calc
          T.sourceLevel m = maxLevel (r (m + 1) T) :=
            (maxLevel_r_succ T m).symm
          _ = maxLevel (r (m + 1) S) := by rw [happrox]
          _ = S.sourceLevel m := maxLevel_r_succ S m
      obtain ⟨p, hpS, hpl, hpx⟩ :=
        S.predecessor_exists m x hx.1 hx.2
      have hpT : p ∈ T.sourceLevel m := by
        rw [htop]
        exact ⟨hpS, hpl⟩
      have hpxlt : p < x := by
        rcases hpx.eq_or_lt with heq | hlt
        · have hlevel : S.levels m = S.levels (m + 1) := by
            calc
              S.levels m = U.level p := hpl.symm
              _ = U.level x := congrArg U.level heq
              _ = S.levels (m + 1) := hx.2
          have hstrict : S.levels m < S.levels (m + 1) :=
            S.levels_strictMono (by omega)
          omega
        · exact hlt
      obtain ⟨c, hpc, hcx⟩ :=
        U.exists_child_le_of_lt hpxlt
      obtain ⟨y, hyT, _⟩ :=
        T.successor_unique m p hpT.1 hpT.2 c hpc
      have hySource : y ∈ T.sourceLevel (m + 1) :=
        ⟨hyT.1, hyT.2.1⟩
      have hyS : y ∈ S.carrier := hTS hyT.1
      obtain ⟨j, hj⟩ := S.carrier_levels y hyS
      have hpy : p < y := hpc.lt.trans_le hyT.2.2
      have hlevel : S.levels m < S.levels j := by
        calc
          S.levels m = U.level p := hpl.symm
          _ < U.level y := U.level_lt hpy
          _ = S.levels j := hj
      have hmj : m + 1 ≤ j := by
        by_contra hnot
        have hjm : j ≤ m := by omega
        have hmono := S.levels_strictMono.monotone hjm
        omega
      obtain ⟨a, ha, hay⟩ :=
        S.exists_sourceLevel_ancestor hmj
          (show y ∈ S.sourceLevel j from ⟨hyS, hj⟩)
      have hclt : U.level c ≤ U.level a := by
        calc
          U.level c = U.level p + 1 := U.level_covBy hpc
          _ = S.levels m + 1 := by rw [hpl]
          _ ≤ S.levels (m + 1) :=
            Nat.succ_le_of_lt
              (S.levels_strictMono (Nat.lt_succ_self m))
          _ = U.level a := ha.2.symm
      have hca : c ≤ a := by
        rcases le_total_of_directed hyT.2.2 hay with hac | hca
        · have heqrank : U.level a = U.level c :=
            le_antisymm (U.level_mono hac) hclt
          have hacEq : a = c :=
            U.eq_of_le_of_level_eq hac heqrank
          rw [hacEq]
        · exact hca
      obtain ⟨w, _, hunique⟩ :=
        S.successor_unique m p hpS hpl c hpc
      have hxw : x = w :=
        hunique x ⟨hx.1, hx.2, hcx⟩
      have haw : a = w :=
        hunique a ⟨ha.1, ha.2, hca⟩
      have hxa : x = a := hxw.trans haw.symm
      refine ⟨y, hySource, ?_⟩
      rw [hxa]
      exact hay

end StrongSubtree

variable {d : ℕ}

/-- Lift an entire heterogeneous boundary tuple through arbitrary
coordinatewise strong refinements preserving their first n source
levels. No synchronization of ambient selected levels is needed. -/
theorem exists_heterogeneousBoundaryTuple_lift
    (P R : Fin d → StrongSubtree U)
    (n : ℕ)
    (hRP : ∀ i, (R i).Refines (P i))
    (happrox : ∀ i, r n (R i) = r n (P i))
    (base : HeterogeneousLevelTuple P n) :
    ∃ lifted : HeterogeneousLevelTuple R n,
      ∀ i, base.1 i ≤ lifted.1 i := by
  classical
  have hex (i : Fin d) :
      ∃ y : U, y ∈ (R i).sourceLevel n ∧ base.1 i ≤ y :=
    (P i).exists_sourceLevel_lift_of_refines
      (R i) (hRP i) (happrox i) (base.2 i)
  let v : Fin d → U := fun i => Classical.choose (hex i)
  have hv (i : Fin d) :
      v i ∈ (R i).sourceLevel n ∧ base.1 i ≤ v i :=
    Classical.choose_spec (hex i)
  exact ⟨⟨v, fun i => (hv i).1⟩, fun i => (hv i).2⟩

end GeneralTree
end Milliken
