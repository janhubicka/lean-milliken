import Milliken.GeneralTree.BoundaryTupleRealization
import Milliken.GeneralTree.CanonicalPigeonhole

/-!
# The exact heterogeneous Halpern--Läuchli implication for A.4

The only combinatorial hypothesis is the finite-dimensional
single-common-level Halpern--Läuchli theorem for the actual strong
successor cones, `HasBoundaryProductHL U`. The proof decodes every
one-step approximation as a synchronized boundary tuple, uses HL on
the finite level product, and reconstructs a genuine strong graft.

`HasBoundaryProductHL` is an explicit *unproved theorem premise* in the
arbitrary-tree development, not an axiom declared in Lean. Thus these
implications do not claim an unconditional proof of unrestricted
Milliken. The homogeneous Hales--Jewett bridge proves the corresponding
homogeneous HL statement separately.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

open StrongSubtree

/-- A one-step strong refinement of the boundary graft must select
its entire new source level from one synchronized level product of
exactly the chosen cone refinements. -/
theorem boundaryTuple_mem_graftFactors
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M)
    (S : StrongSubtree U)
    (hST : S.Refines T)
    (hSR : S.Refines (T.boundaryGraftStrong n F M hF hlevels hM))
    (hStem : r n S = r n T) :
    ∃ k : ℕ, ∀ i : SourceBoundary T n,
      S.boundaryTuple T hST n hStem i ∈ (F i).sourceLevel k := by
  classical
  let R : StrongSubtree U := T.boundaryGraftStrong n F M hF hlevels hM
  let m : ℕ := S.refinementIndex R hSR n
  let k : ℕ := m - n
  have hm : n ≤ m := S.le_refinementIndex R hSR n
  have hmk : n + k = m := by dsimp [k]; omega
  have hRm : R.levels m = M k := by
    calc
      R.levels m = T.boundaryGraftLevels n M m :=
        congrFun (T.boundaryGraftStrong_levels n F M hF hlevels hM) m
      _ = T.boundaryGraftLevels n M (n + k) := by rw [hmk]
      _ = M k := T.boundaryGraftLevels_at n M k
  refine ⟨k, ?_⟩
  intro i
  let x : SourceBoundary T n → U := S.boundaryTuple T hST n hStem
  have hxi : x i ∈ S.sourceLevel n := by
    change S.boundaryTuple T hST n hStem i ∈ S.sourceLevel n
    rw [← S.boundaryTuple_range T hST n hStem]
    exact ⟨i, rfl⟩
  have hxiCarrier : x i ∈ T.boundaryGraftCarrier n F := by
    have hRi : x i ∈ R.carrier := hSR hxi.1
    rw [T.boundaryGraftStrong_carrier n F M hF hlevels hM] at hRi
    exact hRi
  have hxiM : U.level (x i) = M k := by
    calc
      U.level (x i) = S.levels n := hxi.2
      _ = R.levels m := S.levels_refinementIndex R hSR n
      _ = M k := hRm
  have hxSet :
      x i ∈ {z : U | z ∈ T.boundaryGraftCarrier n F ∧
        U.level z = M k} := ⟨hxiCarrier, hxiM⟩
  rw [T.boundaryGraft_level_after n F M hF hlevels hM k] at hxSet
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxSet
  have hiAncestor : i.1 ≤ x i :=
    ((S.boundaryTuple_mem_cone T hST n hStem i).1).2
  have hjAncestor : j.1 ≤ x i := ((hF j) hxj.1).2
  have hiJRank : U.level i.1 = U.level j.1 :=
    i.2.2.trans j.2.2.symm
  have heqIJ : i.1 = j.1 := by
    rcases le_total_of_directed hiAncestor hjAncestor with hji | hij
    · exact (U.eq_of_le_of_level_eq hji hiJRank.symm).symm
    · exact U.eq_of_le_of_level_eq hij hiJRank
  have hij : i = j := Subtype.ext heqIJ
  rw [hij]
  exact hxj

/-- The canonical A.4 pigeonhole property is a *formal consequence*
of precisely the heterogeneous cone-product HL theorem. No extra
pigeonhole statement, thinning axiom, or uniform degree bound occurs. -/
theorem canonicalPigeonhole_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U) :
    HasCanonicalPigeonhole U := by
  classical
  intro n T O
  let χ : (SourceBoundary T n → U) → Fin 2 := fun x =>
    if h : IsSynchronizedBoundaryTuple T n x then
      if boundaryTupleApprox T n x h ∈ O then 1 else 0
    else 0
  obtain ⟨c, M, F, hM, hF, hHom⟩ := hHL T n 2 χ
  have hRef : ∀ i, (F i).Refines (boundaryCones T n i) :=
    fun i => (hF i).1
  have hLevels : ∀ i, (F i).levels = M :=
    fun i => (hF i).2
  let R : StrongSubtree U :=
    T.boundaryGraftStrong n F M hRef hLevels hM
  have hRT : R.Refines T :=
    T.boundaryGraftStrong_refines n F M hRef hLevels hM
  have hRn : r n R = r n T :=
    T.boundaryGraftStrong_approx n F M hRef hLevels hM
  let RS := generalApproximationSystem U
  have hAll :
      ∀ a : SFinite U (n + 1),
        a ∈ RS.oneStepApproximations (r n T) R →
          (a ∈ O ↔ c = 1) := by
    intro a ha
    obtain ⟨S, hSN, hSa⟩ := ha
    have hSR : S.Refines R := hSN.1
    have hStem : r n S = r n T := hSN.2
    have hST : S.Refines T := hSR.trans hRT
    let x : SourceBoundary T n → U := S.boundaryTuple T hST n hStem
    obtain ⟨k, hxF⟩ :=
      boundaryTuple_mem_graftFactors T n F M hRef hLevels hM
        S hST hSR hStem
    have hGood : IsSynchronizedBoundaryTuple T n x := by
      refine ⟨S.refinementIndex T hST n - n, ?_⟩
      intro i
      exact S.boundaryTuple_mem_cone T hST n hStem i
    have hColour : χ x = c := hHom k x hxF
    have hApprox : boundaryTupleApprox T n x hGood = a := by
      apply FiniteApprox.ext_carrier
      calc
        (boundaryTupleApprox T n x hGood).carrier =
            (r n T).carrier ∪ Set.range x :=
          boundaryTupleApprox_carrier T n x hGood
        _ = (r (n + 1) S).carrier :=
          (S.approx_succ_carrier_eq_boundaryTuple T hST n hStem).symm
        _ = a.carrier := congrArg FiniteApprox.carrier hSa
    have hIndicator :
        χ x = (if a ∈ O then (1 : Fin 2) else 0) := by
      simp only [χ, dif_pos hGood, hApprox]
    constructor
    · intro haO
      exact hColour.symm.trans (hIndicator.trans (if_pos haO))
    · intro hc
      by_contra haNotO
      have hcZero : c = (0 : Fin 2) :=
        hColour.symm.trans (hIndicator.trans (if_neg haNotO))
      have hbad : (0 : Fin 2) = 1 := hcZero.symm.trans hc
      exact (by decide : (0 : Fin 2) ≠ 1) hbad
  refine ⟨R, ⟨hRT, hRn⟩, ?_⟩
  by_cases hc : c = (1 : Fin 2)
  · left
    intro a ha
    exact (hAll a ha).mpr hc
  · right
    apply Set.disjoint_left.mpr
    intro a ha haO
    exact hc ((hAll a ha).mp haO)

/-- Published A.4 follows from the genuine finite-dimensional
heterogeneous boundary-product Halpern--Läuchli statement. -/
theorem generalPigeonhole_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U) :
    HasGeneralPigeonhole U :=
  generalPigeonhole_of_canonical U
    (canonicalPigeonhole_of_boundaryProductHL U hHL)

/-- Published A.4 also follows from the general heterogeneous
product Halpern--Läuchli statement by the *proved* finite boundary
reindexing lemma, without introducing a stronger theorem premise. -/
theorem generalPigeonhole_of_generalProductHL
    (U : AmbientTree)
    (hHL : HasGeneralProductHL U) :
    HasGeneralPigeonhole U :=
  generalPigeonhole_of_boundaryProductHL U
    (boundaryProductHL_of_generalProductHL U hHL)

/-- Full A.1--A.4 Ramsey-space data for an arbitrary tree,
conditional exactly on the still-unproved heterogeneous HL theorem. -/
def abstractRamseySpace_of_generalProductHL
    (U : AmbientTree)
    (hHL : HasGeneralProductHL U) :
    RamseySpace.AbstractRamseySpace (generalApproximationSystem U) :=
  abstractRamseySpace_of_pigeonhole U
    (generalPigeonhole_of_generalProductHL U hHL)

end GeneralTree
end Milliken
