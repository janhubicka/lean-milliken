import Milliken.GeneralTree.CodeGeometry

/-!
# Realising a coherent full code as an arbitrary strong subtree

Every infinite sequence of finite approximations whose every finite
prefix is realised determines a unique infinite strong subtree.
The carrier is the union of the intrinsic maximal source frontiers
of the code and the selected levels are recovered from their ambient
ranks. Each of the strong-tree axioms is checked locally in one
finite-prefix realizer: root, source ranks, predecessors and unique
representatives in every ambient immediate child cone.

No Ramsey theorem, general Halpern--Läuchli premise, or global
degree bound enters this reconstruction.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- The recovered root lies below every node in the recovered carrier. -/
theorem codeFrontierNode_root_below
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N)
    {z : U} (hz : z ∈ codeCarrier c) :
    codeFrontierNode c 0 ≤ z := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  obtain ⟨T, hT⟩ := h (n + 1)
  have hnT : z ∈ T.sourceLevel n := by
    rw [← codeFrontier_eq_sourceLevel c T n
      (hT (n + 1) le_rfl)]
    exact hn
  have hroot : codeFrontierNode c 0 ∈ T.sourceLevel 0 := by
    rw [← codeFrontier_eq_sourceLevel c T 0
      (hT 1 (by omega))]
    exact codeFrontierNode_mem c 0
  have hEq : codeFrontierNode c 0 = T.root := by
    rw [T.sourceLevel_zero_eq_singleton] at hroot
    exact hroot
  rw [hEq]
  exact T.root_below z hnT.1

/-- Every recovered carrier node on a positive selected
level has a predecessor on the preceding recovered level. -/
theorem codeCarrier_predecessor_exists
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N)
    (n : ℕ) (z : U)
    (hz : z ∈ codeCarrier c)
    (hzlevel : U.level z = codeSelectedLevels c (n + 1)) :
    ∃ x : U,
      x ∈ codeCarrier c ∧
      U.level x = codeSelectedLevels c n ∧ x ≤ z := by
  have hzFront : z ∈ codeFrontier c (n + 1) :=
    codeCarrier_mem_frontier_of_level c h hz hzlevel
  obtain ⟨T, hT⟩ := h (n + 2)
  have hzT : z ∈ T.sourceLevel (n + 1) := by
    rw [← codeFrontier_eq_sourceLevel c T (n + 1)
      (hT (n + 2) le_rfl)]
    exact hzFront
  obtain ⟨x, hx, hxlevel, hxz⟩ :=
    T.predecessor_exists n z hzT.1 hzT.2
  have hxFront : x ∈ codeFrontier c n := by
    rw [codeFrontier_eq_sourceLevel c T n
      (hT (n + 1) (by omega))]
    exact ⟨hx, hxlevel⟩
  refine ⟨x, codeFrontier_subset_carrier c n hxFront, ?_, hxz⟩
  exact hxlevel.trans
    (codeSelectedLevels_eq c T n
      (hT (n + 1) (by omega))).symm

/-- Every ambient child cone of a recovered source node has
exactly one node on the next selected source level. -/
theorem codeCarrier_successor_unique
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N)
    (n : ℕ) (x : U)
    (hx : x ∈ codeCarrier c)
    (hxlevel : U.level x = codeSelectedLevels c n)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U,
      z ∈ codeCarrier c ∧
      U.level z = codeSelectedLevels c (n + 1) ∧ y ≤ z := by
  have hxFront : x ∈ codeFrontier c n :=
    codeCarrier_mem_frontier_of_level c h hx hxlevel
  obtain ⟨T, hT⟩ := h (n + 2)
  have hxT : x ∈ T.sourceLevel n := by
    rw [← codeFrontier_eq_sourceLevel c T n
      (hT (n + 1) (by omega))]
    exact hxFront
  obtain ⟨z, hz, hunique⟩ :=
    T.successor_unique n x hxT.1 hxT.2 y hxy
  have hzFront : z ∈ codeFrontier c (n + 1) := by
    rw [codeFrontier_eq_sourceLevel c T (n + 1)
      (hT (n + 2) le_rfl)]
    exact ⟨hz.1, hz.2.1⟩
  refine ⟨z, ⟨codeFrontier_subset_carrier c (n + 1) hzFront,
    ?_, hz.2.2⟩, ?_⟩
  · exact hz.2.1.trans
      (codeSelectedLevels_eq c T (n + 1)
        (hT (n + 2) le_rfl)).symm
  · intro w hw
    have hwFront : w ∈ codeFrontier c (n + 1) :=
      codeCarrier_mem_frontier_of_level c h hw.1 hw.2.1
    have hwT : w ∈ T.sourceLevel (n + 1) := by
      rw [← codeFrontier_eq_sourceLevel c T (n + 1)
        (hT (n + 2) le_rfl)]
      exact hwFront
    exact hunique w ⟨hwT.1, hwT.2, hw.2.2⟩

/-- A finite-prefix realizable code has an actual strong subtree
whose carrier and selected level map are intrinsic to the code. -/
noncomputable def pointOfGeneralCode
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N) :
    StrongSubtree U where
  carrier := codeCarrier c
  levels := codeSelectedLevels c
  levels_strictMono := codeSelectedLevels_strictMono c h
  root := codeFrontierNode c 0
  root_mem := codeFrontier_subset_carrier c 0
    (codeFrontierNode_mem c 0)
  root_level := rfl
  root_below := by
    intro z hz
    exact codeFrontierNode_root_below c h hz
  carrier_levels := by
    intro z hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    exact ⟨n, codeFrontier_level c n hn⟩
  predecessor_exists := by
    intro n z hz hzlevel
    exact codeCarrier_predecessor_exists c h n z hz hzlevel
  successor_unique := by
    intro n x hx hxlevel y hxy
    exact codeCarrier_successor_unique c h n x hx hxlevel y hxy

/-- A prefix-realizable full code is recovered exactly by its
point's nth initial strong approximation at every source height. -/
theorem pointOfGeneralCode_approx
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N)
    (n : ℕ) :
    r n (pointOfGeneralCode c h) = c n := by
  obtain ⟨T, hT⟩ := h n
  have hcarrier : (c n).carrier = T.initialPart n := by
    rw [← hT n le_rfl]
    rfl
  apply FiniteApprox.ext_carrier
  change (pointOfGeneralCode c h).initialPart n = (c n).carrier
  rw [hcarrier]
  ext z
  constructor
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hzFront : z ∈ codeFrontier c k :=
      codeCarrier_mem_frontier_of_level c h hz hzlevel
    have hzT : z ∈ T.sourceLevel k := by
      rw [← codeFrontier_eq_sourceLevel c T k
        (hT (k + 1) (by omega))]
      exact hzFront
    exact ⟨hzT.1, k, hk, hzT.2⟩
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hzFront : z ∈ codeFrontier c k := by
      rw [codeFrontier_eq_sourceLevel c T k
        (hT (k + 1) (by omega))]
      exact ⟨hz, hzlevel⟩
    refine ⟨codeFrontier_subset_carrier c k hzFront,
      k, hk, ?_⟩
    exact hzlevel.trans
      (codeSelectedLevels_eq c T k
        (hT (k + 1) (by omega))).symm

end GeneralTree
end Milliken
