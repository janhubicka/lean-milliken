import Milliken.Tree

/-!
# Halpern--Läuchli: strong-subtree formulation

This file fixes the exact theorem statement that is needed in Todorčević,
Theorem 3.2 and later in Lemma 6.1.  We deliberately color the full cartesian
product and impose homogeneity only on level-vectors; this is equivalent to
coloring the disjoint union of the level products and avoids a dependent
Sigma type in downstream arguments.
-/

namespace Milliken

universe u

namespace HalpernLauchli

variable {ι : Type u}

/-- A level map witnessing the levels of a strong embedding. -/
def HasLevels (F : StrongEmbedding ι) (levels : ℕ → ℕ) : Prop :=
  StrictMono levels ∧
    ∀ s : Node ι, (F.toFun s).length = levels s.length

theorem exists_hasLevels (F : StrongEmbedding ι) :
    ∃ levels, HasLevels F levels :=
  F.level_witness

/-- A finite family of strong subtrees has one common level set. -/
def HasCommonLevels {d : ℕ} (F : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ) : Prop :=
  StrictMono levels ∧
    ∀ i s, ((F i).toFun s).length = levels s.length

/-- A tuple of tree nodes lies on one common level. -/
def IsLevelVector {d : ℕ} (x : Fin d → Node ι) : Prop :=
  ∃ n, ∀ i, (x i).length = n

/-- Strong-subtree Halpern--Läuchli, in the form used by Chapter 6.

For every finite coloring of a finite product of trees, there are strong
subtrees with a common level set such that the union of their level products
is monochromatic.  Here all ambient trees are the homogeneous tree
`ι^{<ω}`; cones used in the Milliken pigeonhole proof are represented by
prepending their roots. -/
def StrongSubtreeHL (ι : Type u) [Finite ι] [Nonempty ι] : Prop :=
  ∀ (d colors : ℕ) [NeZero colors]
      (c : (Fin d → Node ι) → Fin colors),
    ∃ color : Fin colors,
      ∃ levels : ℕ → ℕ,
        ∃ F : Fin d → StrongEmbedding ι,
          HasCommonLevels F levels ∧
            ∀ (n : ℕ) (x : Fin d → Node ι),
              (∀ i, (x i).length = n) →
                c (fun i => (F i).toFun (x i)) = color

/-- The dimension-zero case is vacuous and is useful when setting up the
induction on the number of factors. -/
theorem strongSubtreeHL_zero (ι : Type u) :
    ∀ (colors : ℕ) [NeZero colors]
      (c : (Fin 0 → Node ι) → Fin colors),
      ∃ color : Fin colors,
        ∃ levels : ℕ → ℕ,
          ∃ F : Fin 0 → StrongEmbedding ι,
            HasCommonLevels F levels ∧
              ∀ (n : ℕ) (x : Fin 0 → Node ι),
                (∀ i, (x i).length = n) →
                  c (fun i => (F i).toFun (x i)) = color := by
  intro colors hcolors c
  let x0 : Fin 0 → Node ι := fun i => Fin.elim0 i
  let color : Fin colors := c x0
  let F : Fin 0 → StrongEmbedding ι := fun i => Fin.elim0 i
  refine ⟨color, (fun n => n), F, ?_, ?_⟩
  · refine ⟨strictMono_id, ?_⟩
    intro i
    exact Fin.elim0 i
  · intro n x hx
    change c (fun i => (F i).toFun (x i)) = c x0
    have hargs : (fun i => (F i).toFun (x i)) = x0 := by
      funext i
      exact Fin.elim0 i
    rw [hargs]

end HalpernLauchli

end Milliken
