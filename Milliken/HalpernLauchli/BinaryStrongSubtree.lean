import Milliken.HalpernLauchli.LevelHomogeneousFusion
import Milliken.HalpernLauchli.LevelSelector

/-!
# Binary strong-subtree Halpern--Läuchli from HDHL

The fixed-base strengthening of HDHL gives a fusion whose individual source
levels are monochromatic.  Since there are only two colors, one color occurs
on infinitely many fusion levels.  Selecting those source levels and composing
the raw fusion with the canonical level selector yields the usual binary
strong-subtree conclusion.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Binary strong-subtree Halpern--Läuchli in positive dimension follows
from the highly-dense formulation in the same dimension. -/
theorem binaryStrongSubtree_of_hdhl
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (c : (Fin d → Node ι) → Fin 2) :
    ∃ color : Fin 2,
      ∃ levels : ℕ → ℕ,
        ∃ F : Fin d → StrongEmbedding ι,
          HasCommonLevels F levels ∧
            ∀ (n : ℕ) (x : Fin d → Node ι),
              (∀ i, (x i).length = n) →
                c (fun i => (F i).toFun (x i)) = color := by
  classical
  rcases exists_base_levelMonochromaticAbove
      hd hHDHL c with
    ⟨base, ⟨r, hbase⟩, hall⟩
  let colorSeq : ℕ → Fin 2 :=
    fun n => (fusionWitnesses
      hd c base r hbase hall n).color
  rcases Finite.exists_infinite_fiber colorSeq with
    ⟨color, hcolorInf⟩
  have hfiber :
      Set.Infinite (colorSeq ⁻¹' {color}) :=
    Set.infinite_coe_iff.mp hcolorInf
  let selected : ℕ → ℕ :=
    increasingEnumeration
      (colorSeq ⁻¹' {color}) hfiber
  have hselectedMono : StrictMono selected := by
    dsimp [selected]
    exact increasingEnumeration_strictMono _ hfiber
  have hselectedColor :
      ∀ n : ℕ, colorSeq (selected n) = color := by
    intro n
    have hmem :
        selected n ∈ colorSeq ⁻¹' {color} := by
      dsimp [selected]
      exact increasingEnumeration_mem _ hfiber n
    simpa using hmem
  let E : Fin d → StrongEmbedding ι :=
    fun i => branchFusionEmbedding
      hd c base r hbase hall i
  let K : StrongEmbedding ι :=
    levelSelector selected hselectedMono
  let F : Fin d → StrongEmbedding ι :=
    fun i => StrongEmbedding.comp (E i) K
  let levels : ℕ → ℕ :=
    fun n => fusionLevels
      hd c base r hbase hall (selected n)
  have hraw :
      HasCommonLevels E
        (fusionLevels hd c base r hbase hall) := by
    dsimp [E]
    exact branchFusion_commonLevels
      hd c base r hbase hall
  have hlevels : StrictMono levels := by
    dsimp [levels]
    exact
      (fusionLevels_strictMono
        hd c base r hbase hall).comp hselectedMono
  have hcommon : HasCommonLevels F levels := by
    refine ⟨hlevels, ?_⟩
    intro i s
    change
      ((E i).toFun (K.toFun s)).length =
        fusionLevels hd c base r hbase hall
          (selected s.length)
    rw [hraw.2 i (K.toFun s)]
    have hK :
        (K.toFun s).length = selected s.length := by
      dsimp [K]
      exact levelSelector_toFun_length
        selected hselectedMono s
    rw [hK]
  refine ⟨color, levels, F, hcommon, ?_⟩
  intro n x hx
  have hxK :
      ∀ i, (K.toFun (x i)).length = selected n := by
    intro i
    have hlen :=
      levelSelector_toFun_length
        selected hselectedMono (x i)
    rw [hx i] at hlen
    exact hlen
  have hmono :=
    branchFusion_level_monochromatic
      hd c base r hbase hall
      (selected n)
      (fun i => K.toFun (x i))
      hxK
  change
    c (fun i => (E i).toFun (K.toFun (x i))) =
      color
  exact hmono.trans (hselectedColor n)

end HalpernLauchli
end Milliken
