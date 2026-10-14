import Milliken.GeneralTree.BoundaryMilliken
import Milliken.GeneralTree.Identity
import Milliken.GeneralTree.SpliceAmalgamation
import RamseySpace.FiniteColouring

/-!
# Milliken 1979 from the general-tree topological theorem

The original 1979 finite-colouring formulation quantifies over *all*
intrinsic finite height-k strong subtrees. The abstract Ramsey-space
finite-colouring theorem speaks of `FiniteApprox` objects with an
infinite realisation witness. This file proves that *realised* finite
approximations contained in an infinite tree extend to infinite
refinements of that tree. A separate intrinsic-to-realised extension
lemma is still needed to identify the full published quantifier domain.

The geometric extension proof is unconditional and uses the literal
published finitisation (6.3) and A.3(1). This module's last theorem is
a conditional reduction from boundary-product Halpern--Läuchli;
`HeterogeneousUniversalMilliken` later discharges that hypothesis and
exports the unconditional realised-approximation theorem.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Every realized finite strong subtree whose carrier lies in
a strong infinite subtree B extends to a genuine infinite strong
refinement of B realizing precisely that finite approximation.

This relative extension lemma for already realised finite approximations
uses the proved published A.2/A.3 interface, not a homogeneous
alphabet or a new tree-grafting assumption. -/
theorem exists_refinement_realising_general
    (a : SFinite U k) (B : StrongSubtree U)
    (h : a.carrier ⊆ B.carrier) :
    ∃ X : StrongSubtree U,
      X.Refines B ∧ r k X = a := by
  classical
  cases k with
  | zero =>
      obtain ⟨A, hAa⟩ := a.realised
      have ha : a = r 0 A := by
        apply FiniteApprox.ext_carrier
        exact hAa
      refine ⟨B, StrongSubtree.refines_refl B, ?_⟩
      rw [ha]
      exact r_zero_eq B A
  | succ n =>
      obtain ⟨A, hAa⟩ := a.realised
      have haA : r (n + 1) A = a := by
        apply FiniteApprox.ext_carrier
        exact hAa.symm
      obtain ⟨x, hx⟩ := A.sourceLevel_nonempty n
      have hxa : x ∈ a.carrier := by
        rw [← haA]
        exact A.sourceLevel_subset_initialPart
          (Nat.lt_succ_self n) hx
      obtain ⟨j, hj⟩ := B.carrier_levels x (h hxa)
      have hmatch : A.levels n = B.levels j :=
        hx.2.symm.trans hj
      have htop : A.sourceLevel n ⊆ B.sourceLevel j := by
        intro z hz
        have hza : z ∈ a.carrier := by
          rw [← haA]
          exact A.sourceLevel_subset_initialPart
            (Nat.lt_succ_self n) hz
        exact ⟨h hza, hz.2.trans hmatch⟩
      have hcar : a.carrier ⊆ (r (j + 1) B).carrier := by
        intro z hz
        have hzA : z ∈ A.initialPart (n + 1) := by
          change z ∈ (r (n + 1) A).carrier
          rw [haA]
          exact hz
        obtain ⟨_, q, hqn, hlevel⟩ := hzA
        have hqn' : q ≤ n := Nat.le_of_lt_succ hqn
        have hzlevel : U.level z ≤ B.levels j := by
          calc
            U.level z = A.levels q := hlevel
            _ ≤ A.levels n :=
              A.levels_strictMono.monotone hqn'
            _ = B.levels j := hmatch
        exact B.mem_initialPart_of_level_le j (h hz) hzlevel
      have hmax : maxLevel a ⊆ maxLevel (r (j + 1) B) := by
        rw [← haA, maxLevel_r_succ A n,
          maxLevel_r_succ B j]
        exact htop
      have hfin :
          bookLeFin ⟨n + 1, a⟩ ⟨j + 1, r (j + 1) B⟩ :=
        bookLeFin_iff.mpr ⟨hcar, hmax⟩
      obtain ⟨d, hd⟩ :
          ∃ d : ℕ, (generalBookFinitization U).HasDepth a B d :=
        ((generalBookFinitization U).exists_hasDepth_iff a B).mpr
          ⟨j + 1, hfin⟩
      have hself :
          B ∈ (generalApproximationSystem U).levelNeighborhood d B :=
        (generalApproximationSystem U).self_mem_levelNeighborhood d B
      obtain ⟨X, hXB, hXa⟩ :=
        generalAmalgamation_nonempty a B hd hself
      exact ⟨X, hXB, hXa⟩

/-- The realised-finite-approximation version of the 1979 finite-colouring
statement follows from the same explicit boundary-product HL premise
used for Todorčević's unrestricted general-tree A.4. No additional
extension or Ramsey assumption is needed. -/
theorem milliken1979_of_boundaryProductHL
    (U : AmbientTree)
    (hHL : HasBoundaryProductHL U) :
    HasMillikenFiniteColourProperty U := by
  classical
  intro k colors hcolors colour
  let S := generalApproximationSystem U
  let A : StrongSubtree U := identityStrongSubtree U
  have hne : (S.neighborhood (r 0 A) A).Nonempty := by
    exact ⟨A, StrongSubtree.refines_refl A, rfl⟩
  have hTR :
      RamseySpace.IsTopologicalRamseySpaceOnBasicNeighborhoods
        (S := S) :=
    generalMilliken_of_boundaryProductHL U hHL
  obtain ⟨B, _hBA, hhom⟩ :=
    RamseySpace.finiteApproximationColouring
      hTR (r 0 A) A hne colour
  refine ⟨B, colour (r k B), ?_⟩
  intro a ha
  obtain ⟨X, hXB, hXa⟩ :=
    exists_refinement_realising_general a B ha
  have hX :
      X ∈ S.neighborhood (r 0 A) B := by
    refine ⟨hXB, ?_⟩
    exact r_zero_eq X A
  have hB :
      B ∈ S.neighborhood (r 0 A) B := by
    refine ⟨StrongSubtree.refines_refl B, ?_⟩
    exact r_zero_eq B A
  have hcol := hhom X hX B hB
  change colour (r k X) = colour (r k B) at hcol
  rw [hXa] at hcol
  exact hcol

end GeneralTree
end Milliken
