import Milliken.GeneralTree.FrontierUniqueness
import Milliken.GeneralTree.ApproximationSystem
import RamseySpace.Closed

/-!
# Recovering the strong-tree geometry of a coherent infinite approximation code

For a general locally finitely branching rooted ambient tree U, a full
code is a sequence of *realised* finite source approximations a_n.
Every nonempty approximation has a nonempty intrinsic maximal level.
Choose one point of that level to recover its ambient selected rank,
and take the union of all maximal levels to recover its node carrier.

Whenever every finite prefix of the code can be realised by a genuine
strong subtree, these selected ranks strictly increase, each recovered
frontier lies at its recovered rank, and the recovered carrier has an
intrinsic, unique source-level decomposition. These ingredients prepare
the general-tree closedness proof independently of any pigeonhole
assumption or global bound on branching.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- An indexed full sequence of realised finite approximations. -/
abbrev GeneralCode (U : AmbientTree) := (n : ℕ) → SFinite U n

/-- Each nth source frontier is the maximal level of the
(n+1)st finite approximation, intrinsic to the finite carrier. -/
def codeFrontier (c : GeneralCode U) (n : ℕ) : Set U :=
  maxLevel (c (n + 1))

/-- The code frontier is nonempty for every n. -/
theorem codeFrontier_nonempty (c : GeneralCode U) (n : ℕ) :
    (codeFrontier c n).Nonempty :=
  maxLevel_nonempty_succ (c (n + 1))

/-- Canonically choose one ambient node on each code frontier. -/
noncomputable def codeFrontierNode
    (c : GeneralCode U) (n : ℕ) : U :=
  Classical.choose (codeFrontier_nonempty c n)

theorem codeFrontierNode_mem (c : GeneralCode U) (n : ℕ) :
    codeFrontierNode c n ∈ codeFrontier c n :=
  Classical.choose_spec (codeFrontier_nonempty c n)

/-- Recover the selected ambient levels of a full approximation code. -/
noncomputable def codeSelectedLevels
    (c : GeneralCode U) (n : ℕ) : ℕ :=
  U.level (codeFrontierNode c n)

/-- Recover its full carrier from the maximal levels of its approximations. -/
def codeCarrier (c : GeneralCode U) : Set U :=
  ⋃ n : ℕ, codeFrontier c n

/-- The frontier of a prefix-realized code is exactly the indicated
source level of the common realizer. -/
theorem codeFrontier_eq_sourceLevel
    (c : GeneralCode U) (T : StrongSubtree U)
    (n : ℕ) (h : r (n + 1) T = c (n + 1)) :
    codeFrontier c n = T.sourceLevel n := by
  unfold codeFrontier
  rw [← h, maxLevel_r_succ]

/-- The selected ambient rank recovered from a code agrees with
the rank of any realizer of its (n+1)st approximation. -/
theorem codeSelectedLevels_eq
    (c : GeneralCode U) (T : StrongSubtree U)
    (n : ℕ) (h : r (n + 1) T = c (n + 1)) :
    codeSelectedLevels c n = T.levels n := by
  have hfront : codeFrontier c n = T.sourceLevel n :=
    codeFrontier_eq_sourceLevel c T n h
  have hx : codeFrontierNode c n ∈ T.sourceLevel n := by
    rw [← hfront]
    exact codeFrontierNode_mem c n
  exact hx.2

/-- All nodes on the recovered nth frontier have one ambient height. -/
theorem codeFrontier_level
    (c : GeneralCode U) (n : ℕ) {z : U}
    (hz : z ∈ codeFrontier c n) :
    U.level z = codeSelectedLevels c n := by
  obtain ⟨T, hT⟩ := (c (n + 1)).realised
  have h : r (n + 1) T = c (n + 1) := by
    apply FiniteApprox.ext_carrier
    exact hT.symm
  have hfront := codeFrontier_eq_sourceLevel c T n h
  have hlevel := codeSelectedLevels_eq c T n h
  have hzT : z ∈ T.sourceLevel n := by
    rw [← hfront]
    exact hz
  exact hzT.2.trans hlevel.symm

/-- Prefix-realizability in the exact RamseySpace closedness formulation. -/
def CodePrefixRealizable
    (c : GeneralCode U) (N : ℕ) : Prop :=
  ∃ T : StrongSubtree U,
    ∀ n : ℕ, n ≤ N → r n T = c n

/-- The frontier ranks of a prefix-realizable full code strictly increase. -/
theorem codeSelectedLevels_strictMono
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N) :
    StrictMono (codeSelectedLevels c) := by
  intro n m hnm
  obtain ⟨T, hT⟩ := h (m + 1)
  have hn : n + 1 ≤ m + 1 := by omega
  rw [codeSelectedLevels_eq c T n (hT (n + 1) hn),
    codeSelectedLevels_eq c T m (hT (m + 1) le_rfl)]
  exact T.levels_strictMono hnm

/-- A recovered carrier node is on precisely the frontier specified
by its selected rank. -/
theorem codeCarrier_mem_frontier_of_level
    (c : GeneralCode U)
    (h : ∀ N : ℕ, CodePrefixRealizable c N)
    {n : ℕ} {z : U}
    (hz : z ∈ codeCarrier c)
    (hlevel : U.level z = codeSelectedLevels c n) :
    z ∈ codeFrontier c n := by
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hz
  have hrank : codeSelectedLevels c m =
      codeSelectedLevels c n :=
    (codeFrontier_level c m hm).symm.trans hlevel
  have hmn : m = n :=
    (codeSelectedLevels_strictMono c h).injective hrank
  simpa only [hmn] using hm

/-- Every recovered code frontier belongs to the full code carrier. -/
theorem codeFrontier_subset_carrier
    (c : GeneralCode U) (n : ℕ) :
    codeFrontier c n ⊆ codeCarrier c := by
  intro z hz
  exact Set.mem_iUnion.mpr ⟨n, hz⟩

end GeneralTree
end Milliken
