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
      rw [← List.take_append_drop n s,
          ← List.take_append_drop n t, hbval]
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

end BoundaryGraft
end Milliken
