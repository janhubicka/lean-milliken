import Milliken.HalpernLauchli.ReducedCompactness

/-!
# Finite changes of level coded by one finite block alphabet

After compactness, only finitely many sparse levels are relevant.  We can
therefore code the variable gaps between those levels by a single finite
alphabet of blocks of some fixed maximum length `G`.

A source letter is an ambient word of length `G`.  At source level `j`
we use only the first `min (gap j) G` letters of that block.  The unused
tail is harmless padding.  The resulting map is surjective on each selected
ambient level and, more importantly, surjective inside every cone.

Keeping the cap explicit makes the definitions total; later the selected
finite gaps will all be at most `G`, so the cap disappears on the support
of every compactness witness.
-/

namespace Milliken
namespace HalpernLauchli

universe u

variable {ι : Type u}

/-- Fixed-size block alphabet. -/
abbrev LevelBlock (ι : Type u) (G : ℕ) :=
  {s : Node ι // s.length = G}

instance levelBlockFinite [Finite ι] (G : ℕ) :
    Finite (LevelBlock ι G) :=
  (List.finite_length_eq ι G).to_subtype

noncomputable instance levelBlockNonempty
    [Nonempty ι] (G : ℕ) :
    Nonempty (LevelBlock ι G) :=
  ⟨⟨rayNode (ι := ι) G, rayNode_length G⟩⟩

/-- Effective gap used at one source level. -/
def cappedGap (G : ℕ) (gap : ℕ → ℕ) (j : ℕ) : ℕ :=
  min (gap j) G

theorem cappedGap_le (G : ℕ) (gap : ℕ → ℕ) (j : ℕ) :
    cappedGap G gap j ≤ G :=
  min_le_right _ _

/-- Total ambient height traversed by `n` source letters, starting at
source level `j`. -/
def blockSpan (G : ℕ) (gap : ℕ → ℕ) :
    ℕ → ℕ → ℕ
  | _, 0 => 0
  | j, n + 1 =>
      cappedGap G gap j + blockSpan G gap (j + 1) n

@[simp] theorem blockSpan_zero
    (G : ℕ) (gap : ℕ → ℕ) (j : ℕ) :
    blockSpan G gap j 0 = 0 := rfl

@[simp] theorem blockSpan_succ
    (G : ℕ) (gap : ℕ → ℕ) (j n : ℕ) :
    blockSpan G gap j (n + 1) =
      cappedGap G gap j +
        blockSpan G gap (j + 1) n := rfl

/-- Splitting a run of blocks at an intermediate source level splits its
ambient span additively. -/
theorem blockSpan_add
    (G : ℕ) (gap : ℕ → ℕ)
    (j m n : ℕ) :
    blockSpan G gap j (m + n) =
      blockSpan G gap j m +
        blockSpan G gap (j + m) n := by
  induction m generalizing j with
  | zero =>
      simp [blockSpan]
  | succ m ih =>
      rw [show m + 1 + n = (m + n) + 1 by omega]
      simp only [blockSpan_succ]
      rw [ih (j := j + 1)]
      have hidx : j + 1 + m = j + (m + 1) := by omega
      rw [hidx]
      omega

/-- Selected ambient height corresponding to a source level. -/
def blockLevel (G : ℕ) (gap : ℕ → ℕ) (n : ℕ) : ℕ :=
  blockSpan G gap 0 n

theorem blockLevel_add
    (G : ℕ) (gap : ℕ → ℕ)
    (m n : ℕ) :
    blockLevel G gap (m + n) =
      blockLevel G gap m +
        blockSpan G gap m n := by
  simpa [blockLevel] using
    blockSpan_add G gap 0 m n

/-- Decode a block word, starting at source level `j`. -/
def blockMapFrom
    (G : ℕ) (gap : ℕ → ℕ) :
    ℕ → Node (LevelBlock ι G) → Node ι
  | _, [] => []
  | j, b :: s =>
      b.1.take (cappedGap G gap j) ++
        blockMapFrom G gap (j + 1) s

/-- Decode from the root source level. -/
def blockMap
    (G : ℕ) (gap : ℕ → ℕ)
    (s : Node (LevelBlock ι G)) : Node ι :=
  blockMapFrom G gap 0 s

/-- Decoding concatenated source words concatenates their ambient images,
with the source-level offset shifted by the first word length. -/
theorem blockMapFrom_append
    (G : ℕ) (gap : ℕ → ℕ)
    (j : ℕ)
    (s t : Node (LevelBlock ι G)) :
    blockMapFrom G gap j (s ++ t) =
      blockMapFrom G gap j s ++
        blockMapFrom G gap (j + s.length) t := by
  induction s generalizing j with
  | nil =>
      simp [blockMapFrom]
  | cons b s ih =>
      simp only [List.cons_append, blockMapFrom, List.length_cons]
      rw [ih (j := j + 1)]
      simp only [List.append_assoc]
      rw [show j + 1 + s.length =
        j + (s.length + 1) by omega]

theorem blockMap_append
    (G : ℕ) (gap : ℕ → ℕ)
    (s t : Node (LevelBlock ι G)) :
    blockMap G gap (s ++ t) =
      blockMap G gap s ++
        blockMapFrom G gap s.length t := by
  simpa [blockMap] using
    blockMapFrom_append G gap 0 s t

/-- Decoded length is exactly the selected block span. -/
theorem blockMapFrom_length
    (G : ℕ) (gap : ℕ → ℕ)
    (j : ℕ) (s : Node (LevelBlock ι G)) :
    (blockMapFrom G gap j s).length =
      blockSpan G gap j s.length := by
  induction s generalizing j with
  | nil =>
      simp [blockMapFrom, blockSpan]
  | cons b s ih =>
      simp only [blockMapFrom, List.length_append,
        List.length_take, b.2, blockSpan_succ,
        List.length_cons]
      rw [min_eq_left (cappedGap_le G gap j)]
      rw [ih (j := j + 1)]

theorem blockMap_length
    (G : ℕ) (gap : ℕ → ℕ)
    (s : Node (LevelBlock ι G)) :
    (blockMap G gap s).length =
      blockLevel G gap s.length := by
  simpa [blockMap, blockLevel] using
    blockMapFrom_length G gap 0 s

/-- Decoding preserves the tree order. -/
theorem blockMapFrom_prefix
    (G : ℕ) (gap : ℕ → ℕ)
    (j : ℕ) {s t : Node (LevelBlock ι G)}
    (hst : s.IsPrefix t) :
    (blockMapFrom G gap j s).IsPrefix
      (blockMapFrom G gap j t) := by
  rcases hst with ⟨u, rfl⟩
  rw [blockMapFrom_append]
  exact List.prefix_append _ _

theorem blockMap_prefix
    (G : ℕ) (gap : ℕ → ℕ)
    {s t : Node (LevelBlock ι G)}
    (hst : s.IsPrefix t) :
    (blockMap G gap s).IsPrefix
      (blockMap G gap t) :=
  blockMapFrom_prefix G gap 0 hst

/-- Every ambient word of the selected length has a block-code preimage. -/
theorem exists_blockMapFrom_preimage
    [Nonempty ι]
    (G : ℕ) (gap : ℕ → ℕ)
    (j n : ℕ) (t : Node ι)
    (ht : t.length = blockSpan G gap j n) :
    ∃ s : Node (LevelBlock ι G),
      s.length = n ∧
        blockMapFrom G gap j s = t := by
  induction n generalizing j t with
  | zero =>
      have ht0 : t = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa [blockSpan] using ht
      subst t
      exact ⟨[], rfl, rfl⟩
  | succ n ih =>
      let g := cappedGap G gap j
      let head : Node ι := t.take g
      let tail : Node ι := t.drop g
      have htlen :
          t.length =
            g + blockSpan G gap (j + 1) n := by
        simpa [g, blockSpan] using ht
      have hglen : g ≤ t.length := by
        rw [htlen]
        omega
      have hhead : head.length = g := by
        dsimp [head]
        exact List.length_take_of_le hglen
      have htail :
          tail.length =
            blockSpan G gap (j + 1) n := by
        dsimp [tail]
        rw [List.length_drop, htlen]
        omega
      rcases ih (j := j + 1) tail htail with
        ⟨s, hslen, hsmap⟩
      let bword : Node ι :=
        extendToLevel head G
      have hgG : g ≤ G :=
        cappedGap_le G gap j
      have hbword : bword.length = G := by
        dsimp [bword]
        exact length_extendToLevel (by
          simpa [hhead] using hgG)
      let b : LevelBlock ι G := ⟨bword, hbword⟩
      refine ⟨b :: s, ?_, ?_⟩
      · simp [hslen]
      · simp only [blockMapFrom]
        have htake :
            b.1.take g = head := by
          dsimp [b, bword]
          rw [extendToLevel]
          have hghead : g ≤ head.length := by
            omega
          rw [List.take_append_of_le_length
            (l₂ := List.replicate (G - head.length)
              (padLetter ι)) hghead]
          simpa [hhead] using (List.take_all head)
        rw [htake, hsmap]
        dsimp [head, tail]
        exact List.take_append_drop g t

/-- Cone-surjectivity: every selected-level extension of a decoded source
node lifts to a source extension. -/
theorem exists_blockMap_extension
    [Nonempty ι]
    (G : ℕ) (gap : ℕ → ℕ)
    {s : Node (LevelBlock ι G)}
    {n : ℕ} (hsn : s.length ≤ n)
    {t : Node ι}
    (htlen : t.length = blockLevel G gap n)
    (hst : (blockMap G gap s).IsPrefix t) :
    ∃ u : Node (LevelBlock ι G),
      u.length = n ∧
      s.IsPrefix u ∧
      blockMap G gap u = t := by
  let m := s.length
  let r := n - m
  have hnm : n = m + r := by
    dsimp [m, r]
    omega
  have hmaplen :
      (blockMap G gap s).length =
        blockLevel G gap m := by
    simpa [m] using blockMap_length G gap s
  have hlevelsplit :
      blockLevel G gap n =
        blockLevel G gap m +
          blockSpan G gap m r := by
    rw [hnm]
    exact blockLevel_add G gap m r
  rcases hst with ⟨v, htv⟩
  have hvlen :
      v.length = blockSpan G gap m r := by
    have hlen := congrArg List.length htv
    rw [List.length_append, hmaplen, htlen,
      hlevelsplit] at hlen
    omega
  rcases exists_blockMapFrom_preimage
      G gap m r v hvlen with
    ⟨w, hwlen, hwmap⟩
  refine ⟨s ++ w, ?_, List.prefix_append _ _, ?_⟩
  · rw [List.length_append, hwlen, hnm]
  · rw [blockMap_append, hwmap]
    exact htv

end HalpernLauchli
end Milliken
