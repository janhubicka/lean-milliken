import Milliken.HalpernLauchli.BinaryStrongSubtree

/-!
# Finite-color strong-subtree Halpern--Läuchli from the binary case

For a fixed dimension, the binary strong-subtree theorem already implies the
finite-color theorem.  Split off the last color by a binary coloring.  If the
selected binary subtree has color one, the original coloring is already
constant.  Otherwise the last color has been eliminated and we recurse on
the remaining colors.  Common level sets compose coordinatewise.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- The conclusion of the strong-subtree theorem for one fixed coloring. -/
def StrongSubtreeConclusion
    {d colors : ℕ}
    (c : (Fin d → Node ι) → Fin colors) : Prop :=
  ∃ color : Fin colors,
    ∃ levels : ℕ → ℕ,
      ∃ F : Fin d → StrongEmbedding ι,
        HasCommonLevels F levels ∧
          ∀ (n : ℕ) (x : Fin d → Node ι),
            (∀ i, (x i).length = n) →
              c (fun i => (F i).toFun (x i)) = color

/-- The binary case implies every positive finite number of colors, in a
fixed dimension. -/
theorem finiteColorStrongSubtree_of_binary
    [Nonempty ι]
    {d : ℕ}
    (hbin :
      ∀ c : (Fin d → Node ι) → Fin 2,
        StrongSubtreeConclusion c) :
    ∀ colors : ℕ,
      ∀ c : (Fin d → Node ι) → Fin (colors + 1),
        StrongSubtreeConclusion c := by
  intro colors
  induction colors with
  | zero =>
      intro c
      refine ⟨0, (fun n => n),
        (fun _ => StrongEmbedding.id), ?_, ?_⟩
      · refine ⟨strictMono_id, ?_⟩
        intro i s
        rfl
      · intro n x hx
        exact Fin.eq_zero _
  | succ colors ih =>
      intro c
      let last : Fin (colors + 2) :=
        Fin.last (colors + 1)
      let bcol : (Fin d → Node ι) → Fin 2 :=
        fun x => if c x = last then 1 else 0
      rcases hbin bcol with
        ⟨b, flevels, F, hFcommon, hFmono⟩
      by_cases hb : b = (1 : Fin 2)
      · refine ⟨last, flevels, F, hFcommon, ?_⟩
        intro n x hx
        have hmono := hFmono n x hx
        rw [hb] at hmono
        by_contra hnot
        simp [bcol, hnot] at hmono
      · have hb0 : b = (0 : Fin 2) := by
          apply Fin.ext
          have hbval : b.val < 2 := b.isLt
          have hbne : b.val ≠ 1 := by
            intro hval
            apply hb
            apply Fin.ext
            simpa using hval
          omega
        let pull :
            (Fin d → Node ι) → Fin (colors + 2) :=
          fun x => c (fun i => (F i).toFun (x i))
        let reduced :
            (Fin d → Node ι) → Fin (colors + 1) :=
          fun x =>
            if h : pull x = last then
              0
            else
              ⟨(pull x).val, by
                have hlt := (pull x).isLt
                have hne : (pull x).val ≠ colors + 1 := by
                  intro hv
                  apply h
                  apply Fin.ext
                  simpa [last] using hv
                omega⟩
        rcases ih reduced with
          ⟨color, glevels, G, hGcommon, hGmono⟩
        let H : Fin d → StrongEmbedding ι :=
          fun i => StrongEmbedding.comp (F i) (G i)
        let levels : ℕ → ℕ :=
          fun n => flevels (glevels n)
        have hHcommon : HasCommonLevels H levels := by
          dsimp [H, levels]
          exact hFcommon.comp hGcommon
        refine ⟨color.castSucc, levels, H, hHcommon, ?_⟩
        intro n x hx
        let gx : Fin d → Node ι :=
          fun i => (G i).toFun (x i)
        have hgx :
            ∀ i, (gx i).length = glevels n := by
          intro i
          dsimp [gx]
          rw [hGcommon.2 i, hx i]
        have hnotLast : pull gx ≠ last := by
          intro hlast
          have hmono := hFmono (glevels n) gx hgx
          rw [hb0] at hmono
          simp [bcol, pull, hlast] at hmono
        have hred :
            reduced gx = color :=
          hGmono n x hx
        have hcast :
            (reduced gx).castSucc = pull gx := by
          apply Fin.ext
          simp [reduced, hnotLast]
        change pull gx = color.castSucc
        exact hcast.symm.trans (congrArg Fin.castSucc hred)

/-- If binary strong-subtree Halpern--Läuchli is available in every
dimension, then so is the full finite-color theorem. -/
theorem strongSubtreeHL_of_binary
    [Nonempty ι]
    (hbin :
      ∀ d : ℕ,
        ∀ c : (Fin d → Node ι) → Fin 2,
          StrongSubtreeConclusion c) :
    StrongSubtreeHL ι := by
  intro d colors hcolors c
  cases colors with
  | zero =>
      exact (hcolors.out rfl).elim
  | succ colors =>
      exact
        finiteColorStrongSubtree_of_binary
          (hbin d) colors c

end HalpernLauchli
end Milliken
