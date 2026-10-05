import Milliken.BranchEmbedding
import Milliken.HalpernLauchli.Asymmetric

/-!
# Selecting a subsequence of source levels

If `a : ℕ → ℕ` is strictly increasing, there is a canonical strong
self-embedding of the homogeneous tree whose source level `n` lands on
target level `a n`.  It preserves each branch label literally and fills the
gaps between selected levels with the fixed padding letter.

This is the small thinning device needed to pass from a fusion whose level
products are individually monochromatic to one whose level products all have
the same color.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- One step of the level-selector fold.  The natural-number component
records the number of source letters already processed. -/
noncomputable def levelSelectorStep
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (S : ℕ × Node ι) (a : ι) :
    ℕ × Node ι :=
  (S.1 + 1,
    extendToLevel (child S.2 a) (levels (S.1 + 1)))

@[simp] theorem levelSelectorStep_fst
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (S : ℕ × Node ι) (a : ι) :
    (levelSelectorStep levels S a).1 = S.1 + 1 := rfl

theorem levelSelectorStep_length
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (S : ℕ × Node ι) (a : ι)
    (hS : S.2.length = levels S.1) :
    (levelSelectorStep levels S a).2.length =
      levels (S.1 + 1) := by
  have hlt :
      levels S.1 < levels (S.1 + 1) :=
    hlevels (Nat.lt_succ_self S.1)
  have hchild :
      (child S.2 a).length ≤ levels (S.1 + 1) := by
    simp [child, hS]
    omega
  exact length_extendToLevel hchild

/-- Fold a source word from an arbitrary selector state. -/
noncomputable def levelSelectorFold
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (S : ℕ × Node ι)
    (s : Node ι) :
    ℕ × Node ι :=
  List.foldl (levelSelectorStep levels) S s

theorem levelSelectorFold_index
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (S : ℕ × Node ι)
    (s : Node ι) :
    (levelSelectorFold levels S s).1 =
      S.1 + s.length := by
  induction s generalizing S with
  | nil =>
      simp [levelSelectorFold]
  | cons a s ih =>
      simp only [levelSelectorFold, List.foldl]
      change
        (levelSelectorFold levels
          (levelSelectorStep levels S a) s).1 =
          S.1 + (a :: s).length
      rw [ih]
      simp [levelSelectorStep]
      omega

theorem levelSelectorFold_length
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (S : ℕ × Node ι)
    (hS : S.2.length = levels S.1)
    (s : Node ι) :
    (levelSelectorFold levels S s).2.length =
      levels (levelSelectorFold levels S s).1 := by
  induction s generalizing S with
  | nil =>
      simpa [levelSelectorFold] using hS
  | cons a s ih =>
      simp only [levelSelectorFold, List.foldl]
      apply ih
      exact levelSelectorStep_length levels hlevels S a hS

/-- Run the selector from its canonical root state. -/
noncomputable def runLevelSelector
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (s : Node ι) :
    ℕ × Node ι :=
  levelSelectorFold levels
    (0, rayNode (ι := ι) (levels 0)) s

theorem runLevelSelector_index
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (s : Node ι) :
    (runLevelSelector (ι := ι) levels s).1 = s.length := by
  unfold runLevelSelector
  rw [levelSelectorFold_index]
  simp

theorem runLevelSelector_length
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (s : Node ι) :
    (runLevelSelector (ι := ι) levels s).2.length =
      levels s.length := by
  have h :=
    levelSelectorFold_length
      levels hlevels
      (0, rayNode (ι := ι) (levels 0))
      (by simp)
      s
  change
    (levelSelectorFold levels
      (0, rayNode (ι := ι) (levels 0)) s).2.length =
      levels s.length
  have hidx :
      (levelSelectorFold levels
        (0, rayNode (ι := ι) (levels 0)) s).1 =
        s.length := by
    simpa using
      (levelSelectorFold_index levels
        (0, rayNode (ι := ι) (levels 0)) s)
  exact h.trans (congrArg levels hidx)

/-- Node map of the selector. -/
noncomputable def levelSelectorFun
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (s : Node ι) : Node ι :=
  (runLevelSelector (ι := ι) levels s).2

theorem runLevelSelector_child
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (s : Node ι) (a : ι) :
    runLevelSelector (ι := ι) levels (child s a) =
      levelSelectorStep levels
        (runLevelSelector (ι := ι) levels s) a := by
  simp [runLevelSelector, levelSelectorFold, child,
    List.foldl_append, levelSelectorStep]

theorem levelSelectorFun_length
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (s : Node ι) :
    (levelSelectorFun (ι := ι) levels s).length =
      levels s.length :=
  runLevelSelector_length levels hlevels s

theorem levelSelectorFun_branch
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (s : Node ι) (a : ι) :
    (child (levelSelectorFun (ι := ι) levels s) a).IsPrefix
      (levelSelectorFun (ι := ι) levels (child s a)) := by
  change
    (child
      (runLevelSelector (ι := ι) levels s).2 a).IsPrefix
      (runLevelSelector (ι := ι) levels (child s a)).2
  rw [runLevelSelector_child]
  exact prefix_extendToLevel _ _

/-- Strong self-embedding selecting exactly the prescribed source levels. -/
noncomputable def levelSelector
    [Nonempty ι]
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels) :
    StrongEmbedding ι :=
  StrongEmbedding.ofBranchLevels
    (levelSelectorFun (ι := ι) levels)
    levels hlevels
    (levelSelectorFun_length levels hlevels)
    (levelSelectorFun_branch levels)

end HalpernLauchli
end Milliken
