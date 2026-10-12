import Milliken.GeneralTree.HeterogeneousBranchFusion
import Milliken.GeneralTree.SubsequenceStrong
import Milliken.HalpernLauchli.LevelSelector

/-!
# Binary strong-subtree Halpern--Läuchli from heterogeneous HDHL

The actual-child branch fusion gives strong subtrees with the same
selected *source indices* in every factor, but the monochromatic
colour may depend on the index. A finite-range colour sequence has
an infinite constant-colour fibre. Selecting precisely those source
indices using the genuine deeper-root subsequenceStrong constructor
makes every selected product level monochromatic in one colour.

The input factors need not be isomorphic or share ambient level
maps. If they do share one, so do the resulting strong refinements.
The only non-elementary premise is HDHL in this same dimension for
these very factors; no additional HL axiom or global degree bound.
-/

namespace Milliken
namespace GeneralTree

open HalpernLauchli

variable {U : AmbientTree} {d : ℕ}

/-- Binary strong-tree HL on arbitrary finite products of locally
finite strong-tree factors, *conditional only on their HDHL property*.
The output shares a single increasing source-index subsequence f,
and any shared ambient level map is therefore preserved. -/
theorem heterogeneousBinaryStrongHL_of_hdhl
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL P)
    (c : (Fin d → U) → Fin 2) :
    ∃ color : Fin 2,
      ∃ f : ℕ → ℕ,
        ∃ F : Fin d → StrongSubtree U,
          StrictMono f ∧
            (∀ i, (F i).Refines (P i) ∧
              (F i).levels = fun k => (P i).levels (f k)) ∧
            (∀ k (x : Fin d → U),
              (∀ i, x i ∈ (F i).sourceLevel k) →
              c x = color) := by
  classical
  obtain ⟨r, base, hall⟩ :=
    heterogeneous_exists_base_levelMonochromaticAbove
      P hd hHDHL c
  let E : Fin d → StrongSubtree U :=
    heterogeneousFusionTrees P c hd base hall
  let colors : ℕ → Fin 2 :=
    fun k => (heterogeneousFusionWitnesses
      P c hd base hall k).color
  obtain ⟨color, hInfiniteFibre⟩ :=
    Finite.exists_infinite_fiber colors
  have hInfinite : (colors ⁻¹' {color}).Infinite :=
    Set.infinite_coe_iff.mp hInfiniteFibre
  let selected : ℕ → ℕ :=
    increasingEnumeration (colors ⁻¹' {color}) hInfinite
  have hselected : StrictMono selected :=
    increasingEnumeration_strictMono _ hInfinite
  have hcolor : ∀ k, colors (selected k) = color := by
    intro k
    have hmem := increasingEnumeration_mem
      (colors ⁻¹' {color}) hInfinite k
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hmem
  let f : ℕ → ℕ :=
    fun k => heterogeneousFusionLevels P c hd base hall (selected k)
  have hf : StrictMono f :=
    (heterogeneousFusionLevels_strictMono P c hd base hall).comp
      hselected
  let F : Fin d → StrongSubtree U :=
    fun i => (E i).subsequenceStrong selected hselected
  refine ⟨color, f, F, hf, ?_, ?_⟩
  · intro i
    constructor
    · exact ((E i).subsequenceStrong_refines
        selected hselected).trans
        (heterogeneousFusionTrees_refines P c hd base hall i)
    · calc
        (F i).levels =
            fun k => (E i).levels (selected k) :=
          (E i).subsequenceStrong_levels selected hselected
        _ = fun k => (P i).levels (f k) := by
          funext k
          exact congrFun
            (heterogeneousFusionTrees_levels P c hd base hall i)
            (selected k)
  · intro k x hx
    have hPicked :
        ∀ i, x i ∈ (E i).sourceLevel (selected k) := by
      intro i
      exact ((E i).subsequenceStrong_sourceLevel_subset
        selected hselected k) (hx i)
    have hc := heterogeneousFusionTrees_monochromatic_at
      P c hd base hall (selected k) x hPicked
    exact hc.trans (hcolor k)

/-- For synchronized input factors, the binary theorem produces a
family with one literal common selected *ambient* level map. -/
theorem heterogeneousBinarySynchronizedHL_of_hdhl
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (hHDHL : HasHeterogeneousHDHL P)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (c : (Fin d → U) → Fin 2) :
    ∃ color : Fin 2,
      ∃ M : ℕ → ℕ,
        ∃ F : Fin d → StrongSubtree U,
          StrictMono M ∧
            (∀ i, (F i).Refines (P i) ∧
              (F i).levels = M) ∧
            (∀ k (x : Fin d → U),
              (∀ i, x i ∈ (F i).sourceLevel k) →
              c x = color) := by
  obtain ⟨color, f, F, hf, hF, hmono⟩ :=
    heterogeneousBinaryStrongHL_of_hdhl P hd hHDHL c
  let M : ℕ → ℕ := fun k => L (f k)
  have hL : StrictMono L := by
    let i0 : Fin d := ⟨0, hd⟩
    rw [← hP i0]
    exact (P i0).levels_strictMono
  refine ⟨color, M, F, hL.comp hf, ?_, hmono⟩
  intro i
  obtain ⟨hinc, hlev⟩ := hF i
  refine ⟨hinc, ?_⟩
  rw [hlev, hP i]

end GeneralTree
end Milliken
