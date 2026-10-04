import Milliken.Cone

/-!
# Boundary grafting of strong subtrees

Source-tree form of Todorčević's construction (6.8): keep all source nodes
below a height `n` fixed, and attach a strong embedding above every boundary
node of length `n`.
-/

namespace Milliken

universe u

def LevelNode (ι : Type u) (n : ℕ) :=
  {s : Node ι // s.length = n}

namespace BoundaryGraft

variable {ι : Type u} {n : ℕ}

def boundaryPrefix (n : ℕ) (s : Node ι) (hs : n ≤ s.length) :
    LevelNode ι n :=
  ⟨s.take n, List.length_take_of_le hs⟩

def HasCommonLevels (F : LevelNode ι n → StrongEmbedding ι) : Prop :=
  ∃ levels : ℕ → ℕ,
    StrictMono levels ∧
      ∀ b s, ((F b).toFun s).length = levels s.length

noncomputable def graftFun
    (F : LevelNode ι n → StrongEmbedding ι)
    (s : Node ι) : Node ι :=
  if hs : s.length < n then s
  else
    let b := boundaryPrefix n s (le_of_not_gt hs)
    b.1 ++ (F b).toFun (s.drop n)

theorem graftFun_of_lt
    (F : LevelNode ι n → StrongEmbedding ι)
    (s : Node ι) (hs : s.length < n) :
    graftFun F s = s := by
  simp [graftFun, hs]

theorem graftFun_of_ge
    (F : LevelNode ι n → StrongEmbedding ι)
    (s : Node ι) (hs : n ≤ s.length) :
    graftFun F s =
      (boundaryPrefix n s hs).1 ++
        (F (boundaryPrefix n s hs)).toFun (s.drop n) := by
  simp [graftFun, not_lt.mpr hs]

theorem boundaryPrefix_eq_of_prefix
    {s t : Node ι} (hst : s.IsPrefix t)
    (hs : n ≤ s.length) :
    boundaryPrefix n s hs =
      boundaryPrefix n t (hs.trans hst.length_le) := by
  apply Subtype.ext
  have htake := hst.take n
  apply htake.eq_of_length
  rw [List.length_take_of_le hs,
      List.length_take_of_le (hs.trans hst.length_le)]

theorem graftFun_prefix_mono
    (F : LevelNode ι n → StrongEmbedding ι)
    {s t : Node ι} (hst : s.IsPrefix t) :
    (graftFun F s).IsPrefix (graftFun F t) := by
  by_cases hs : s.length < n
  · by_cases ht : t.length < n
    · rw [graftFun_of_lt F s hs, graftFun_of_lt F t ht]
      exact hst
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [graftFun_of_lt F s hs, graftFun_of_ge F t htge]
      have hpre : s.IsPrefix (boundaryPrefix n t htge).1 := by
        have htake := hst.take n
        have hsTake : s.take n = s :=
          (List.take_eq_self_iff s).2 (by omega)
        simpa [boundaryPrefix, hsTake] using htake
      exact hpre.trans (List.prefix_append _ _)
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := hsge.trans hst.length_le
    rw [graftFun_of_ge F s hsge, graftFun_of_ge F t htge]
    have hb :
        boundaryPrefix n s hsge =
          boundaryPrefix n t htge :=
      boundaryPrefix_eq_of_prefix hst hsge
    rw [hb]
    exact StrongEmbedding.prefix_append_left
      (boundaryPrefix n t htge).1
      ((F (boundaryPrefix n t htge)).prefix_mono (hst.drop n))

/-- The graft map reflects prefixes. -/
theorem graftFun_prefix_reflect
    (F : LevelNode ι n → StrongEmbedding ι)
    {s t : Node ι}
    (h : (graftFun F s).IsPrefix (graftFun F t)) :
    s.IsPrefix t := by
  by_cases hs : s.length < n
  · by_cases ht : t.length < n
    · rwa [graftFun_of_lt F s hs, graftFun_of_lt F t ht] at h
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [graftFun_of_lt F s hs, graftFun_of_ge F t htge] at h
      have hlen :
          s.length ≤ (boundaryPrefix n t htge).1.length := by
        rw [(boundaryPrefix n t htge).2]
        exact Nat.le_of_lt hs
      have hsb :
          s.IsPrefix (boundaryPrefix n t htge).1 :=
        (List.isPrefix_append_of_length hlen).mp h
      exact hsb.trans (List.take_prefix n t)
  · have hsge : n ≤ s.length := le_of_not_gt hs
    by_cases ht : t.length < n
    · rw [graftFun_of_ge F s hsge, graftFun_of_lt F t ht] at h
      have hlen := h.length_le
      have hbLen : (boundaryPrefix n s hsge).1.length = n :=
        (boundaryPrefix n s hsge).2
      rw [List.length_append, hbLen] at hlen
      omega
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [graftFun_of_ge F s hsge, graftFun_of_ge F t htge] at h
      have hboundary :
          (boundaryPrefix n s hsge).1.IsPrefix
            ((boundaryPrefix n t htge).1 ++
              (F (boundaryPrefix n t htge)).toFun (t.drop n)) :=
        (List.prefix_append _ _).trans h
      have hbp :
          (boundaryPrefix n s hsge).1.IsPrefix
            (boundaryPrefix n t htge).1 :=
        (List.isPrefix_append_of_length (by
          rw [(boundaryPrefix n s hsge).2,
              (boundaryPrefix n t htge).2])).mp hboundary
      have hbval :
          (boundaryPrefix n s hsge).1 =
            (boundaryPrefix n t htge).1 :=
        hbp.eq_of_length (by
          rw [(boundaryPrefix n s hsge).2,
              (boundaryPrefix n t htge).2])
      have hb :
          boundaryPrefix n s hsge =
            boundaryPrefix n t htge :=
        Subtype.ext hbval
      rw [hb] at h
      have hdrop :
          (s.drop n).IsPrefix (t.drop n) :=
        (F (boundaryPrefix n t htge)).prefix_reflect
          (StrongEmbedding.prefix_cancel_left
            (boundaryPrefix n t htge).1 h)
      have htake : s.take n = t.take n := by
        simpa [boundaryPrefix] using hbval
      rw [← List.take_append_drop n s,
          ← List.take_append_drop n t, htake]
      exact StrongEmbedding.prefix_append_left _ hdrop

/-- The graft node map is injective. -/
theorem graftFun_injective
    (F : LevelNode ι n → StrongEmbedding ι) :
    Function.Injective (graftFun F) := by
  intro s t hst
  have hs :
      s.IsPrefix t := graftFun_prefix_reflect F (by
        rw [hst])
  have ht :
      t.IsPrefix s := graftFun_prefix_reflect F (by
        rw [hst])
  exact hs.eq_of_length (le_antisymm hs.length_le ht.length_le)

/-- Dropping a fixed prefix commutes with adjoining one child once the
drop point lies inside the original node. -/
theorem drop_child_of_le
    (s : Node ι) (i : ι) (h : n ≤ s.length) :
    (child s i).drop n = child (s.drop n) i := by
  simpa [child] using
    (List.drop_append_of_le_length (l₂ := [i]) h)

/-- The graft satisfies the strong branch condition. -/
theorem graftFun_branch
    (F : LevelNode ι n → StrongEmbedding ι)
    (s : Node ι) (i : ι) :
    (child (graftFun F s) i).IsPrefix
      (graftFun F (child s i)) := by
  by_cases hs : s.length < n
  · by_cases hc : (child s i).length < n
    · rw [graftFun_of_lt F s hs, graftFun_of_lt F (child s i) hc]
    · have hcge : n ≤ (child s i).length := le_of_not_gt hc
      have hslen : s.length + 1 = n := by
        simp [child] at hcge
        omega
      rw [graftFun_of_lt F s hs, graftFun_of_ge F (child s i) hcge]
      have hb :
          (boundaryPrefix n (child s i) hcge).1 = child s i := by
        dsimp [boundaryPrefix]
        apply (List.take_eq_self_iff _).2
        simpa [child] using hslen.le
      rw [hb]
      exact List.prefix_append _ _
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have hcge : n ≤ (child s i).length := by
      simp [child]
      omega
    rw [graftFun_of_ge F s hsge, graftFun_of_ge F (child s i) hcge]
    have hb :
        boundaryPrefix n s hsge =
          boundaryPrefix n (child s i) hcge :=
      boundaryPrefix_eq_of_prefix (List.prefix_append s [i]) hsge
    rw [hb, drop_child_of_le (n := n) s i hsge]
    simpa [child, List.append_assoc] using
      StrongEmbedding.prefix_append_left
        (boundaryPrefix n (child s i) hcge).1
        ((F (boundaryPrefix n (child s i) hcge)).branch (s.drop n) i)

/-- The graft also reflects the strong branch label. -/
theorem graftFun_branch_reflect
    (F : LevelNode ι n → StrongEmbedding ι)
    (s t : Node ι) (i : ι)
    (h :
      (child (graftFun F s) i).IsPrefix
        (graftFun F t)) :
    (child s i).IsPrefix t := by
  by_cases hs : s.length < n
  · by_cases hc : (child s i).length < n
    · have heq :
          child (graftFun F s) i =
            graftFun F (child s i) := by
        rw [graftFun_of_lt F s hs,
            graftFun_of_lt F (child s i) hc]
      apply graftFun_prefix_reflect F
      rwa [← heq]
    · have hcge : n ≤ (child s i).length := le_of_not_gt hc
      have hslen : (child s i).length = n := by
        simp [child] at hs hcge ⊢
        omega
      have hprefix :
          (child s i).IsPrefix (graftFun F t) := by
        simpa [graftFun_of_lt F s hs] using h
      have htlen : n ≤ t.length := by
        have hlen := hprefix.length_le
        by_cases ht : t.length < n
        · rw [graftFun_of_lt F t ht] at hlen
          omega
        · exact le_of_not_gt ht
      have htake :
          (graftFun F t).take n = t.take n := by
        rw [graftFun_of_ge F t htlen]
        have hnlen :
            n ≤ (boundaryPrefix n t htlen).1.length := by
          rw [(boundaryPrefix n t htlen).2]
        rw [List.take_append_of_le_length hnlen]
        apply (List.take_eq_self_iff _).2
        rw [(boundaryPrefix n t htlen).2]
      have hchildTake :
          (graftFun F t).take n = child s i := by
        have hp := hprefix.take n
        have hleft : (child s i).take n = child s i := by
          rw [List.take_eq_self_iff]
          omega
        rw [hleft] at hp
        exact (hp.eq_of_length (by
          rw [List.length_take_of_le]
          · exact hslen
          · have := hprefix.length_le
            omega)).symm
      have hst : child s i = t.take n := by
        rw [← htake]
        exact hchildTake.symm
      rw [hst]
      exact List.take_prefix n t
  · have hsge : n ≤ s.length := le_of_not_gt hs
    by_cases ht : t.length < n
    · have hgn : n ≤ (graftFun F s).length := by
        rw [graftFun_of_ge F s hsge, List.length_append,
            (boundaryPrefix n s hsge).2]
        omega
      have hlen := h.length_le
      rw [graftFun_of_lt F t ht] at hlen
      simp [child] at hlen
      omega
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [graftFun_of_ge F s hsge,
          graftFun_of_ge F t htge] at h
      have hboundary :
          (boundaryPrefix n s hsge).1.IsPrefix
            ((boundaryPrefix n t htge).1 ++
              (F (boundaryPrefix n t htge)).toFun (t.drop n)) := by
        exact (List.prefix_append _ _).trans
          ((List.prefix_append _ [i]).trans h)
      have hbp :
          (boundaryPrefix n s hsge).1.IsPrefix
            (boundaryPrefix n t htge).1 :=
        (List.isPrefix_append_of_length (by
          rw [(boundaryPrefix n s hsge).2,
              (boundaryPrefix n t htge).2])).mp hboundary
      have hbval :
          (boundaryPrefix n s hsge).1 =
            (boundaryPrefix n t htge).1 :=
        hbp.eq_of_length (by
          rw [(boundaryPrefix n s hsge).2,
              (boundaryPrefix n t htge).2])
      have hb :
          boundaryPrefix n s hsge =
            boundaryPrefix n t htge :=
        Subtype.ext hbval
      rw [hb] at h
      have hdrop :
          (child (s.drop n) i).IsPrefix (t.drop n) := by
        apply (F (boundaryPrefix n t htge)).branch_reflect
        have h' :
            (boundaryPrefix n t htge).1 ++
                child ((F (boundaryPrefix n t htge)).toFun (s.drop n)) i
              <+:
            (boundaryPrefix n t htge).1 ++
                (F (boundaryPrefix n t htge)).toFun (t.drop n) := by
          simpa [child, List.append_assoc] using h
        exact StrongEmbedding.prefix_cancel_left
          (boundaryPrefix n t htge).1 h'
      have htake : s.take n = t.take n := by
        simpa [boundaryPrefix] using hbval
      rw [← List.take_append_drop n (child s i),
          ← List.take_append_drop n t]
      have htakeChild :
          (child s i).take n = s.take n := by
        simpa [child] using
          List.take_append_of_le_length (l₂ := [i]) hsge
      rw [htakeChild, htake]
      exact StrongEmbedding.prefix_append_left _
        (by simpa [drop_child_of_le (n := n) s i hsge] using hdrop)

/-- Target lengths of the graft depend only on source length when the
boundary embeddings have common level sets. -/
theorem graftFun_length_eq_of_length_eq
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F)
    (s t : Node ι) (hst : s.length = t.length) :
    (graftFun F s).length = (graftFun F t).length := by
  rcases hF with ⟨levels, hmono, hlevels⟩
  by_cases hs : s.length < n
  · have ht : t.length < n := by simpa [hst] using hs
    rw [graftFun_of_lt F s hs, graftFun_of_lt F t ht, hst]
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := by simpa [hst] using hsge
    rw [graftFun_of_ge F s hsge, graftFun_of_ge F t htge,
        List.length_append, List.length_append,
        (boundaryPrefix n s hsge).2, (boundaryPrefix n t htge).2,
        hlevels, hlevels, List.length_drop, List.length_drop, hst]

/-- Source-level strict increase gives strict increase of graft target
levels. -/
theorem graftFun_length_lt_of_length_lt
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F)
    (s t : Node ι) (hst : s.length < t.length) :
    (graftFun F s).length < (graftFun F t).length := by
  rcases hF with ⟨levels, hmono, hlevels⟩
  by_cases hs : s.length < n
  · by_cases ht : t.length < n
    · rw [graftFun_of_lt F s hs, graftFun_of_lt F t ht]
      exact hst
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [graftFun_of_lt F s hs, graftFun_of_ge F t htge,
          List.length_append, (boundaryPrefix n t htge).2, hlevels,
          List.length_drop]
      have hnonneg : 0 ≤ levels (t.length - n) := Nat.zero_le _
      omega
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := hsge.trans hst.le
    rw [graftFun_of_ge F s hsge, graftFun_of_ge F t htge,
        List.length_append, List.length_append,
        (boundaryPrefix n s hsge).2, (boundaryPrefix n t htge).2,
        hlevels, hlevels, List.length_drop, List.length_drop]
    have hsub : s.length - n < t.length - n := by omega
    exact Nat.add_lt_add_left (hmono hsub) n

/-- Canonical common level map for the graft. -/
noncomputable def graftLevels [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (k : ℕ) : ℕ :=
  (graftFun F (List.replicate k (Classical.choice
    (inferInstance : Nonempty ι)))).length

theorem graftLevels_strictMono [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrictMono (graftLevels F) := by
  intro k l hkl
  exact graftFun_length_lt_of_length_lt F hF
    (List.replicate k (Classical.choice
      (inferInstance : Nonempty ι)))
    (List.replicate l (Classical.choice
      (inferInstance : Nonempty ι))) (by simpa using hkl)

theorem graftFun_same_level [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F)
    (s : Node ι) :
    (graftFun F s).length = graftLevels F s.length := by
  exact graftFun_length_eq_of_length_eq F hF s
    (List.replicate s.length (Classical.choice
      (inferInstance : Nonempty ι))) (by simp)

/-- Package the boundary graft as a strong embedding. -/
noncomputable def graft [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrongEmbedding ι where
  toFun := graftFun F
  injective := graftFun_injective F
  prefix_mono := graftFun_prefix_mono F
  prefix_reflect := graftFun_prefix_reflect F
  branch := graftFun_branch F
  branch_reflect := graftFun_branch_reflect F
  level_witness := ⟨graftLevels F, graftLevels_strictMono F hF,
    graftFun_same_level F hF⟩

/-- The graft fixes every source node below the boundary height. -/
theorem graft_toFun_of_lt [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F)
    (s : Node ι) (hs : s.length < n) :
    (graft F hF).toFun s = s :=
  graftFun_of_lt F s hs

end BoundaryGraft
end Milliken
