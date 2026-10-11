import Milliken.HalpernLauchli.HighlyDenseObstruction

/-!
# Remark 3.8: selecting levels for the highly-dense formulation

Todorčević's Remark 3.8 compresses a finitely branching tree to a suitably
chosen set of levels.  In the compressed tree a somewhere-dense matrix in
the complement would occur between two selected levels; the latter can be
chosen recursively so far apart that high density in the original tree
forbids this.

The present file formalizes exactly that level-selection argument while
keeping the nodes in the original homogeneous tree.  What remains for the
fully source-faithful Chapter 3 reconstruction is to instantiate the reduced
dichotomy on this level-restricted tree.  That last step is separated
explicitly because the branching of the compressed tree depends on the
selected level gap.

The key point proved here is therefore not conditional: every highly dense
set admits a strictly increasing selected-level sequence on which its
complement contains no restricted somewhere-dense matrix.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- One density scale witnessing high density at target scale `k`. -/
noncomputable def highlyDenseScale
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) : ℕ :=
  Classical.choose (hP k)

theorem highlyDenseScale_spec
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ)
    (M : Matrix ι d)
    (hM : M.DenseAt (highlyDenseScale hP k)) :
    ProductDenseAt (P ∩ M.carrier) k :=
  (Classical.choose_spec (hP k)) M hM

/-- Selected levels used in Remark 3.8.

Level zero is the original root level.  The next selected level is chosen
strictly above the current level, above the requested target `k`, and
above the high-density scale attached to the current selected level. -/
noncomputable def remark38Levels
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
      max (remark38Levels hP k n + 1)
        (max k
          (highlyDenseScale hP (remark38Levels hP k n)))

@[simp] theorem remark38Levels_zero
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) :
    remark38Levels hP k 0 = 0 := rfl

@[simp] theorem remark38Levels_succ
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k n : ℕ) :
    remark38Levels hP k (n + 1) =
      max (remark38Levels hP k n + 1)
        (max k
          (highlyDenseScale hP (remark38Levels hP k n))) := rfl

theorem remark38Levels_lt_succ
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k n : ℕ) :
    remark38Levels hP k n <
      remark38Levels hP k (n + 1) := by
  rw [remark38Levels_succ]
  exact (Nat.lt_succ_self _).trans_le
    (Nat.le_max_left _ _)

theorem remark38Levels_strictMono
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) :
    StrictMono (remark38Levels hP k) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact remark38Levels_lt_succ hP k n

theorem remark38Levels_target_le_succ
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k n : ℕ) :
    k ≤ remark38Levels hP k (n + 1) := by
  rw [remark38Levels_succ]
  exact (Nat.le_max_left k
      (highlyDenseScale hP (remark38Levels hP k n))).trans
    (Nat.le_max_right _ _)

theorem remark38Levels_scale_le_succ
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k n : ℕ) :
    highlyDenseScale hP (remark38Levels hP k n) ≤
      remark38Levels hP k (n + 1) := by
  rw [remark38Levels_succ]
  exact (Nat.le_max_right k
      (highlyDenseScale hP (remark38Levels hP k n))).trans
    (Nat.le_max_right _ _)

/-- Somewhere density measured in the tree compressed to `levels`.

A base must lie on one selected level and the dense target on a strictly
later selected level. -/
def RestrictedSomewhereDense
    {d : ℕ}
    (levels : ℕ → ℕ)
    (M : Matrix ι d) : Prop :=
  ∃ p q : ℕ, p < q ∧
    ∃ base : Fin d → Node ι,
      IsLevelVectorAt (levels p) base ∧
        M.DenseAbove base (levels q)

/-- A set contains a somewhere-dense matrix in the selected-level tree. -/
def ContainsRestrictedSomewhereDense
    {d : ℕ}
    (levels : ℕ → ℕ)
    (P : Set (Fin d → Node ι)) : Prop :=
  ∃ M : Matrix ι d,
    RestrictedSomewhereDense levels M ∧
      M.carrier ⊆ P

/-- The recursive level choice from Remark 3.8 kills every
selected-level somewhere-dense matrix in the complement of a highly dense
set. -/
theorem no_restrictedSomewhereDense_compl_of_highlyDense
    [Nonempty ι]
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) :
    ¬ ContainsRestrictedSomewhereDense
      (remark38Levels hP k) Pᶜ := by
  classical
  rintro ⟨M, ⟨p, q, hpq, base, hbase, hMdense⟩, hMsub⟩
  let levels : ℕ → ℕ := remark38Levels hP k
  have hmono : StrictMono levels := by
    dsimp [levels]
    exact remark38Levels_strictMono hP k
  have hpq' : p + 1 ≤ q := Nat.succ_le_of_lt hpq
  have hnextq : levels (p + 1) ≤ levels q :=
    hmono.monotone hpq'
  have hbaseNext :
      ∀ i, (base i).length < levels (p + 1) := by
    intro i
    rw [hbase i]
    exact hmono (Nat.lt_succ_self p)
  have hMnext :
      M.DenseAbove base (levels (p + 1)) :=
    M.denseAbove_of_le hnextq hMdense
  let A : Matrix ι d :=
    M.fillOutsideAbove base (levels q)
  have hAnext :
      A.DenseAt (levels (p + 1)) := by
    dsimp [A]
    exact M.fillOutsideAbove_denseAt
      base hMnext hbaseNext hnextq
  have hscale :
      highlyDenseScale hP (levels p) ≤ levels (p + 1) := by
    dsimp [levels]
    exact remark38Levels_scale_le_succ hP k p
  have hA :
      A.DenseAt (highlyDenseScale hP (levels p)) :=
    A.denseAt_of_le hscale hAnext
  have hPA :
      ProductDenseAt (P ∩ A.carrier) (levels p) :=
    highlyDenseScale_spec hP (levels p) A hA
  rcases hPA base hbase with
    ⟨y, hyPA, hbasey⟩
  have hyM : y ∈ M.carrier := by
    dsimp [A] at hyPA
    exact M.carrier_mem_of_fillOutsideAbove_of_prefix
      base hyPA.2 hbasey
  exact (hMsub hyM) hyPA.1

/-- The reduced dichotomy for the tree whose source level `n` is the
ambient level `levels n`.

This is the exact interface needed to finish Remark 3.8.  It is stated
separately from the homogeneous reduced dichotomy because the compressed
tree has level-dependent branching when the gaps in `levels` vary. -/
def RestrictedReducedDichotomy
    (ι : Type u) (d : ℕ)
    (levels : ℕ → ℕ) : Prop :=
  ∀ P : Set (Fin d → Node ι),
    (¬ ContainsRestrictedSomewhereDense levels Pᶜ) →
      ∃ M : Matrix ι d,
        M.DenseAt (levels 1) ∧ M.carrier ⊆ P

/-- Formal content of Remark 3.8: reduced dichotomy on the selected-level
trees implies the highly-dense formulation on the original homogeneous
tree. -/
theorem hdhl_of_restrictedReduced
    [Nonempty ι]
    {d : ℕ}
    (hred :
      ∀ (P : Set (Fin d → Node ι))
        (hP : HighlyDense P) (k : ℕ),
        RestrictedReducedDichotomy
          ι d (remark38Levels hP k)) :
    HDHL ι d := by
  intro P hP k hk
  have hno :
      ¬ ContainsRestrictedSomewhereDense
        (remark38Levels hP k) Pᶜ :=
    no_restrictedSomewhereDense_compl_of_highlyDense hP k
  rcases hred P hP k P hno with
    ⟨M, hM, hMsub⟩
  have hk1 : k ≤ remark38Levels hP k 1 := by
    simpa using remark38Levels_target_le_succ hP k 0
  exact ⟨M, M.denseAt_of_le hk1 hM, hMsub⟩

end HalpernLauchli
end Milliken
