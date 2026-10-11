import Milliken.HalpernLauchli.SelectedLevelDensity
import Milliken.HalpernLauchli.SparseFiniteHL

/-!
# Finite Halpern--Läuchli on selected levels

The compactness part of Theorem 3.9 is insensitive to variable branching:
all finite witnesses still live in the ambient homogeneous tree.  The only
change is the witness-production step.  Selected-level HDHL supplies either
a dense color-zero matrix at a selected level, or arbitrarily deep
color-one cone matrices above one fixed selected-level base.

We package the latter using the existing SparseFiniteHLWitness with the
selected sequence S.levels, then reuse the existing finite-witness
compactness and transport machinery.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- Selected levels dominate their rank because they start at zero and are
strictly increasing. -/
theorem rank_le_level
    (S : Selection) (n : ℕ) :
    n ≤ S.levels n := by
  induction n with
  | zero =>
      simp [S.zero]
  | succ n ih =>
      have hstep :
          S.levels n < S.levels (n + 1) :=
        S.strictMono (Nat.lt_succ_self n)
      omega

theorem level_pos_of_rank_pos
    (S : Selection) {n : ℕ}
    (hn : 0 < n) :
    0 < S.levels n := by
  exact hn.trans_le (rank_le_level S n)

/-- Every binary coloring has a finite sparse witness aligned with the
selected levels. -/
theorem exists_sparseFiniteHLWitness_of_hdhl
    [Finite ι] [Nonempty ι]
    (S : Selection)
    {d k : ℕ}
    (hHDHL : HDHL (ι := ι) S d)
    (hk : 0 < k)
    (c : BinaryColoring ι d) :
    ∃ W : SparseFiniteHLWitness ι d (S.levels k) S.levels,
      c ∈ W.cylinder := by
  classical
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  rcases asymmetric_of_hdhl S hHDHL K0 with hzero | hone
  · rcases hzero k hk with ⟨M, hMdense, hMsub⟩
    let N : Matrix ι d := M.finiteDenseCore hMdense
    let W : SparseFiniteHLWitness
        ι d (S.levels k) S.levels := {
      M := N
      color := 0
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseCore_coord_finite hMdense
      shape := Or.inl ⟨rfl, by
        dsimp [N]
        exact M.finiteDenseCore_dense hMdense⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier :=
      M.finiteDenseCore_subset hMdense hx
    exact hMsub hxM
  · rcases hone with ⟨p, base, hbase, hall⟩
    rcases hall (p + 1) (Nat.lt_succ_self p) with
      ⟨M, hMdense, hMsub⟩
    let N : Matrix ι d :=
      M.finiteDenseAboveCore base hMdense
    have hNsparse :
        SparseSomewhereDense S.levels N := by
      refine ⟨p, base, hbase, ?_⟩
      dsimp [N]
      exact M.finiteDenseAboveCore_dense base hMdense
    let W : SparseFiniteHLWitness
        ι d (S.levels k) S.levels := {
      M := N
      color := 1
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseAboveCore_coord_finite base hMdense
      shape := Or.inr ⟨rfl, hNsparse⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier :=
      M.finiteDenseAboveCore_subset base hMdense hx
    have hx1 : x ∈ K0ᶜ := hMsub hxM
    have hne : c x ≠ (0 : Fin 2) := by
      intro h0
      exact hx1 h0
    exact Fin.eq_one_of_ne_zero (c x) hne

/-- The selected sparse-witness cylinders cover all binary colorings. -/
theorem sparseFiniteHLWitness_cover
    [Finite ι] [Nonempty ι]
    (S : Selection)
    {d k : ℕ}
    (hHDHL : HDHL (ι := ι) S d)
    (hk : 0 < k) :
    (Set.univ : Set (BinaryColoring ι d)) ⊆
      ⋃ W : SparseFiniteHLWitness
          ι d (S.levels k) S.levels,
        W.cylinder := by
  intro c hc
  rcases exists_sparseFiniteHLWitness_of_hdhl
      S hHDHL hk c with ⟨W, hW⟩
  exact Set.mem_iUnion.2 ⟨W, hW⟩

/-- Compactness leaves only finitely many selected sparse witnesses. -/
theorem exists_sparseFiniteHLWitness_subcover
    [Finite ι] [Nonempty ι]
    (S : Selection)
    {d k : ℕ}
    (hHDHL : HDHL (ι := ι) S d)
    (hk : 0 < k) :
    ∃ F : Finset
        (SparseFiniteHLWitness ι d (S.levels k) S.levels),
      (Set.univ : Set (BinaryColoring ι d)) ⊆
        ⋃ W ∈ F, W.cylinder := by
  classical
  exact isCompact_univ.elim_finite_subcover
    (fun W : SparseFiniteHLWitness
      ι d (S.levels k) S.levels => W.cylinder)
    (fun W => W.cylinder_isOpen)
    (sparseFiniteHLWitness_cover S hHDHL hk)

/-- Finite Halpern--Läuchli aligned with an arbitrary selected-level tree. -/
theorem sparseFiniteHL_of_hdhl
    [Finite ι] [Nonempty ι]
    (S : Selection)
    {d k : ℕ}
    (hHDHL : HDHL (ι := ι) S d)
    (hk : 0 < k) :
    ∃ l : ℕ, ∀ M : Matrix ι d,
      M.DenseAt (S.levels l) →
      ∀ K0 : Set (Fin d → Node ι),
        (∃ M1 : Matrix ι d,
            SparseSomewhereDense S.levels M1 ∧
            M1.carrier ⊆ M.carrier ∩ K0ᶜ) ∨
        (∃ M0 : Matrix ι d,
            M0.DenseAt (S.levels k) ∧
            M0.carrier ⊆ M.carrier ∩ K0) := by
  classical
  rcases exists_sparseFiniteHLWitness_subcover
      S hHDHL hk with ⟨F, hcover⟩
  let L : ℕ := sparseWitnessFamilyBound F
  let l : ℕ := max k L
  have hLlevel : L ≤ S.levels l := by
    have hLl : L ≤ l := by
      dsimp [l]
      exact Nat.le_max_right _ _
    exact hLl.trans (rank_le_level S l)
  refine ⟨l, ?_⟩
  intro M hM K0
  let mapTuple : (Fin d → Node ι) → (Fin d → Node ι) :=
    fun x i => extendIntoDense M hM i (x i)
  let c : BinaryColoring ι d :=
    fun x => if mapTuple x ∈ K0 then 0 else 1
  have hc :
      c ∈ ⋃ W ∈ F, W.cylinder :=
    hcover (Set.mem_univ c)
  simp only [Set.mem_iUnion] at hc
  rcases hc with ⟨W, hWF, hcW⟩
  have hbound :
      ∀ i s, s ∈ W.M.coord i →
        s.length ≤ S.levels l := by
    intro i s hs
    have hL : s.length ≤ L :=
      sparseWitness_length_le_familyBound hWF hs
    exact hL.trans hLlevel
  let N : Matrix ι d :=
    transportSparseWitness W M hM
  have hNsubM : N.carrier ⊆ M.carrier := by
    dsimp [N]
    exact transportSparseWitness_subset W M hM
  rcases W.shape with hzero | hone
  · right
    rcases hzero with ⟨hcolor, hWdense⟩
    have hNdense : N.DenseAt (S.levels k) := by
      dsimp [N]
      exact transportSparseWitness_dense
        W M hM hbound hWdense
    refine ⟨N, hNdense, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    rcases exists_source_of_mem_transportSparseWitness
        W M hM hz with ⟨x, hxW, hxmap⟩
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 0 :=
      (hcW x hxW).trans hcolor
    by_contra hzK
    have hcx1 : c x = 1 := by
      simp [c, hmap, hzK]
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcx.symm.trans hcx1)
  · left
    rcases hone with ⟨hcolor, hWsparse⟩
    have hNsparse :
        SparseSomewhereDense S.levels N := by
      dsimp [N]
      exact transportSparseWitness_sparse
        W M hM hbound hWsparse
    refine ⟨N, hNsparse, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    intro hzK
    rcases exists_source_of_mem_transportSparseWitness
        W M hM hz with ⟨x, hxW, hxmap⟩
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 1 :=
      (hcW x hxW).trans hcolor
    have hcx0 : c x = 0 := by
      simp [c, hmap, hzK]
    exact (by decide : (1 : Fin 2) ≠ 0)
      (hcx.symm.trans hcx0)

end SelectedLevelTree
end HalpernLauchli
end Milliken
