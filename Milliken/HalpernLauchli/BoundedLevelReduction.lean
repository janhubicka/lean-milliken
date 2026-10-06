import Milliken.HalpernLauchli.FiniteLevelBlocks
import Milliken.HalpernLauchli.Remark38

/-!
# Reduced dichotomy for bounded selected-level gaps

If the gaps between selected levels are bounded by one integer `G`, the
compressed tree is a quotient of the homogeneous tree over the finite block
alphabet `LevelBlock ι G`.

At source level `j`, a block contributes only its first
`levels (j+1) - levels j` letters.  The unused tail is irrelevant.
The block decoder from `FiniteLevelBlocks` is surjective on every selected
level and, more importantly, surjective inside every cone.  Consequently
dense and somewhere-dense matrices transport from the homogeneous block tree
to the selected-level tree.

This proves the Remark 3.8 reduction whenever the selected gaps are globally
bounded, and isolates the genuinely new case to unbounded level-dependent
branching.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Gap between two consecutive selected ambient levels. -/
def selectedGap (levels : ℕ → ℕ) (n : ℕ) : ℕ :=
  levels (n + 1) - levels n

theorem levels_add_selectedGap
    {levels : ℕ → ℕ}
    (hmono : StrictMono levels) (n : ℕ) :
    levels n + selectedGap levels n = levels (n + 1) := by
  unfold selectedGap
  exact Nat.add_sub_of_le
    (hmono.monotone (Nat.le_succ n))

/-- With a cap above every actual gap, the block decoder reaches exactly the
prescribed selected levels. -/
theorem blockLevel_selectedGap
    (G : ℕ) {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ n, selectedGap levels n ≤ G)
    (n : ℕ) :
    blockLevel G (selectedGap levels) n = levels n := by
  induction n with
  | zero =>
      simpa [blockLevel, hzero]
  | succ n ih =>
      calc
        blockLevel G (selectedGap levels) (n + 1) =
            blockLevel G (selectedGap levels) n +
              blockSpan G (selectedGap levels) n 1 := by
                simpa using
                  (blockLevel_add G (selectedGap levels) n 1)
        _ =
            blockLevel G (selectedGap levels) n +
              cappedGap G (selectedGap levels) n := by
                simp [blockSpan]
        _ =
            blockLevel G (selectedGap levels) n +
              selectedGap levels n := by
                rw [cappedGap, min_eq_left (hgap n)]
        _ = levels n + selectedGap levels n := by
              rw [ih]
        _ = levels (n + 1) :=
              levels_add_selectedGap hmono n

theorem blockMap_length_selectedGap
    (G : ℕ) {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ n, selectedGap levels n ≤ G)
    (s : Node (LevelBlock ι G)) :
    (blockMap G (selectedGap levels) s).length =
      levels s.length := by
  rw [blockMap_length,
    blockLevel_selectedGap G hzero hmono hgap]

/-- Every node on a selected ambient level has a block-code preimage. -/
theorem exists_blockMap_preimage_selectedGap
    [Nonempty ι]
    (G : ℕ) {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ n, selectedGap levels n ≤ G)
    (n : ℕ) (t : Node ι)
    (ht : t.length = levels n) :
    ∃ s : Node (LevelBlock ι G),
      s.length = n ∧
        blockMap G (selectedGap levels) s = t := by
  apply exists_blockMapFrom_preimage
    G (selectedGap levels) 0 n t
  rw [← blockLevel]
  rw [blockLevel_selectedGap G hzero hmono hgap]
  exact ht

/-- Cone-surjectivity specialized to the selected levels. -/
theorem exists_blockMap_extension_selectedGap
    [Nonempty ι]
    (G : ℕ) {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ n, selectedGap levels n ≤ G)
    {s : Node (LevelBlock ι G)}
    {n : ℕ} (hsn : s.length ≤ n)
    {t : Node ι}
    (ht : t.length = levels n)
    (hst :
      (blockMap G (selectedGap levels) s).IsPrefix t) :
    ∃ u : Node (LevelBlock ι G),
      u.length = n ∧
      s.IsPrefix u ∧
      blockMap G (selectedGap levels) u = t := by
  apply exists_blockMap_extension
    G (selectedGap levels) hsn
  · rw [blockLevel_selectedGap G hzero hmono hgap]
    exact ht
  · exact hst

/-- Coordinatewise block decoding. -/
def blockTupleMap
    {d G : ℕ} (gap : ℕ → ℕ)
    (x : Fin d → Node (LevelBlock ι G)) :
    Fin d → Node ι :=
  fun i => blockMap G gap (x i)

/-- Pull a product set back along coordinatewise block decoding. -/
def blockPullback
    {d G : ℕ} (gap : ℕ → ℕ)
    (P : Set (Fin d → Node ι)) :
    Set (Fin d → Node (LevelBlock ι G)) :=
  {x | blockTupleMap gap x ∈ P}

namespace Matrix

/-- Decode every coordinate of a block-tree matrix. -/
def blockImage
    {d G : ℕ} (gap : ℕ → ℕ)
    (M : Matrix (LevelBlock ι G) d) :
    Matrix ι d where
  coord := fun i => blockMap G gap '' M.coord i

theorem exists_source_of_mem_blockImage
    {d G : ℕ} (gap : ℕ → ℕ)
    (M : Matrix (LevelBlock ι G) d)
    {z : Fin d → Node ι}
    (hz : z ∈ (M.blockImage gap).carrier) :
    ∃ x ∈ M.carrier, blockTupleMap gap x = z := by
  classical
  choose x hxM hx using fun i => hz i
  refine ⟨x, ?_, ?_⟩
  · intro i
    exact hxM i
  · funext i
    exact hx i

theorem blockImage_carrier_subset_of_pullback
    {d G : ℕ} (gap : ℕ → ℕ)
    (M : Matrix (LevelBlock ι G) d)
    (P : Set (Fin d → Node ι))
    (hM : M.carrier ⊆ blockPullback gap P) :
    (M.blockImage gap).carrier ⊆ P := by
  intro z hz
  rcases M.exists_source_of_mem_blockImage gap hz with
    ⟨x, hxM, hxz⟩
  have hxP : blockTupleMap gap x ∈ P := hM hxM
  rwa [hxz] at hxP

/-- Global density transports from the block tree to the corresponding
selected ambient level. -/
theorem blockImage_denseAt_selectedGap
    [Nonempty ι]
    {d G n : ℕ} {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ j, selectedGap levels j ≤ G)
    (M : Matrix (LevelBlock ι G) d)
    (hM : M.DenseAt n) :
    (M.blockImage (selectedGap levels)).DenseAt (levels n) := by
  intro i t ht
  change t.length = levels n at ht
  rcases exists_blockMap_preimage_selectedGap
      G hzero hmono hgap n t ht with
    ⟨s, hslen, hsmap⟩
  rcases hM i
      (show s ∈ treeLevel (ι := LevelBlock ι G) n from hslen) with
    ⟨y, hyM, hsy⟩
  refine ⟨blockMap G (selectedGap levels) y, ?_, ?_⟩
  · exact ⟨y, hyM, rfl⟩
  · rw [← hsmap]
    exact blockMap_prefix G (selectedGap levels) hsy

/-- Cone density transports between corresponding selected levels. -/
theorem blockImage_denseAbove_selectedGap
    [Nonempty ι]
    {d G p q : ℕ} {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ j, selectedGap levels j ≤ G)
    (hpq : p ≤ q)
    (M : Matrix (LevelBlock ι G) d)
    (base : Fin d → Node (LevelBlock ι G))
    (hbase : IsLevelVectorAt p base)
    (hM : M.DenseAbove base q) :
    (M.blockImage (selectedGap levels)).DenseAbove
      (blockTupleMap (selectedGap levels) base) (levels q) := by
  intro i t ht
  have hbaseq : (base i).length ≤ q := by
    rw [hbase i]
    exact hpq
  rcases exists_blockMap_extension_selectedGap
      G hzero hmono hgap hbaseq ht.2 ht.1 with
    ⟨s, hslen, hbases, hsmap⟩
  rcases hM i
      (show s ∈ coneLevel (base i) q from
        ⟨hbases, hslen⟩) with
    ⟨y, hyM, hsy⟩
  refine ⟨blockMap G (selectedGap levels) y, ?_, ?_⟩
  · exact ⟨y, hyM, rfl⟩
  · rw [← hsmap]
    exact blockMap_prefix G (selectedGap levels) hsy

end Matrix

/-- A somewhere-dense block-tree matrix decodes to a somewhere-dense matrix
in the selected-level sense. -/
theorem restrictedSomewhereDense_blockImage
    [Nonempty ι]
    {d G : ℕ} (hd : 0 < d)
    {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ j, selectedGap levels j ≤ G)
    (M : Matrix (LevelBlock ι G) d)
    (hM : M.SomewhereDense) :
    RestrictedSomewhereDense levels
      (M.blockImage (selectedGap levels)) := by
  classical
  rcases hM with ⟨base, q, hbase, hMdense⟩
  let i0 : Fin d := ⟨0, hd⟩
  have hq : 0 < q := by
    have h := hbase i0
    omega
  let p : ℕ := q - 1
  let raised : Fin d → Node (LevelBlock ι G) :=
    fun i => extendToLevel (base i) p
  have hbasep : ∀ i, (base i).length ≤ p := by
    intro i
    have h := hbase i
    dsimp [p]
    omega
  have hraisedLevel : IsLevelVectorAt p raised := by
    intro i
    dsimp [raised]
    exact length_extendToLevel (hbasep i)
  have hprefix :
      ∀ i, (base i).IsPrefix (raised i) := by
    intro i
    dsimp [raised]
    exact prefix_extendToLevel _ _
  have hpq : p < q := by
    dsimp [p]
    omega
  have hMraised : M.DenseAbove raised q := by
    intro i s hs
    have hsbase : s ∈ coneLevel (base i) q :=
      ⟨(hprefix i).trans hs.1, hs.2⟩
    exact hMdense i hsbase
  let targetBase : Fin d → Node ι :=
    blockTupleMap (selectedGap levels) raised
  refine ⟨p, q, hpq, targetBase, ?_, ?_⟩
  · intro i
    dsimp [targetBase, blockTupleMap]
    rw [blockMap_length_selectedGap
      G hzero hmono hgap, hraisedLevel i]
  · dsimp [targetBase]
    exact Matrix.blockImage_denseAbove_selectedGap
      hzero hmono hgap hpq.le M raised
      hraisedLevel hMraised

/-- Ordinary reduced dichotomy on one homogeneous block alphabet implies the
restricted reduced dichotomy whenever all selected gaps fit into that
alphabet. -/
theorem restrictedReduced_of_boundedGaps
    [Finite ι] [Nonempty ι]
    {d G : ℕ} (hd : 0 < d)
    {levels : ℕ → ℕ}
    (hzero : levels 0 = 0)
    (hmono : StrictMono levels)
    (hgap : ∀ j, selectedGap levels j ≤ G)
    (hred : ReducedDichotomy (LevelBlock ι G) d) :
    RestrictedReducedDichotomy ι d levels := by
  classical
  intro P hno
  let gap : ℕ → ℕ := selectedGap levels
  let Q : Set (Fin d → Node (LevelBlock ι G)) :=
    blockPullback gap P
  have hnoQ : ¬ ContainsSomewhereDense Qᶜ := by
    rintro ⟨M, hMsome, hMsub⟩
    let N : Matrix ι d := M.blockImage gap
    have hNsome : RestrictedSomewhereDense levels N := by
      dsimp [N, gap]
      exact restrictedSomewhereDense_blockImage
        hd hzero hmono hgap M hMsome
    have hMsub' :
        M.carrier ⊆ blockPullback gap Pᶜ := by
      intro x hxM
      have hxQ : x ∈ Qᶜ := hMsub hxM
      change blockTupleMap gap x ∈ Pᶜ
      intro hxP
      apply hxQ
      change blockTupleMap gap x ∈ P
      exact hxP
    have hNsub : N.carrier ⊆ Pᶜ := by
      dsimp [N]
      exact M.blockImage_carrier_subset_of_pullback
        gap Pᶜ hMsub'
    exact hno ⟨N, hNsome, hNsub⟩
  rcases hred Q hnoQ with
    ⟨M, hMdense, hMsub⟩
  let N : Matrix ι d := M.blockImage gap
  refine ⟨N, ?_, ?_⟩
  · dsimp [N, gap]
    exact Matrix.blockImage_denseAt_selectedGap
      hzero hmono hgap M hMdense
  · have hMsub' :
        M.carrier ⊆ blockPullback gap P := by
      simpa [Q] using hMsub
    dsimp [N]
    exact M.blockImage_carrier_subset_of_pullback
      gap P hMsub'

end HalpernLauchli
end Milliken
