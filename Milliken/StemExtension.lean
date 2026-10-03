import Milliken.Stem
import Milliken.Cone

/-!
# Extending a finite strong stem

Assume a nonempty finite approximation `a` is contained in an infinite
strong subtree `A`.  Pull `a` back through `A` using `stemPreimage`.
Above the last source level of `a`, extend by keeping that pulled-back
last-level node and appending the untouched source suffix.

This file first proves the list-decomposition, level, and prefix lemmas.
The resulting function is then packaged as a `StrongEmbedding`.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- The source node of the last stem level below a node. -/
def stemTopPrefix (n : ℕ) (hpos : 0 < n) (s : Node ι) :
    FiniteNode ι n :=
  ⟨s.take (n - 1), by
    have hle : (s.take (n - 1)).length ≤ n - 1 := by
      rw [List.length_take]
      exact Nat.min_le_left _ _
    omega⟩

theorem stemTopPrefix_length_of_ge (n : ℕ) (hpos : 0 < n)
    (s : Node ι) (hs : n ≤ s.length) :
    (stemTopPrefix n hpos s).1.length = n - 1 := by
  dsimp [stemTopPrefix]
  exact List.length_take_of_le (by omega)

theorem stemTopPrefix_append_drop (n : ℕ) (hpos : 0 < n)
    (s : Node ι) :
    (stemTopPrefix n hpos s).1 ++ s.drop (n - 1) = s := by
  exact List.take_append_drop (n - 1) s

/-- Extension of a pulled-back finite stem to all source nodes. -/
noncomputable def stemExtensionFun {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) : Node ι :=
  if hs : s.length < n then
    stemPreimage a A hA ⟨s, hs⟩
  else
    stemPreimage a A hA (stemTopPrefix n hpos s) ++
      s.drop (n - 1)

theorem stemExtensionFun_of_lt {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) (hs : s.length < n) :
    stemExtensionFun hpos a A hA s =
      stemPreimage a A hA (⟨s, hs⟩ : FiniteNode ι n) := by
  simp [stemExtensionFun, hs]

theorem stemExtensionFun_of_ge {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) (hs : n ≤ s.length) :
    stemExtensionFun hpos a A hA s =
      stemPreimage a A hA (stemTopPrefix n hpos s) ++
        s.drop (n - 1) := by
  simp [stemExtensionFun, not_lt.mpr hs]

/-- A short prefix remains a prefix of the last stem prefix of a longer
node. -/
theorem prefix_stemTopPrefix_of_prefix {n : ℕ} (hpos : 0 < n)
    {s t : Node ι} (hst : s.IsPrefix t)
    (hs : s.length < n) :
    s.IsPrefix (stemTopPrefix n hpos t).1 := by
  have hsle : s.length ≤ n - 1 := by omega
  have htake := hst.take (n - 1)
  have hsTake : s.take (n - 1) = s :=
    (List.take_eq_self_iff s).2 hsle
  simpa [stemTopPrefix, hsTake] using htake

/-- Once both nodes are at or above the last stem level, taking that stem
prefix is constant along a prefix relation. -/
theorem stemTopPrefix_eq_of_prefix {n : ℕ} (hpos : 0 < n)
    {s t : Node ι} (hst : s.IsPrefix t)
    (hs : n ≤ s.length) :
    stemTopPrefix n hpos s = stemTopPrefix n hpos t := by
  apply Subtype.ext
  have htake := hst.take (n - 1)
  apply htake.eq_of_length
  rw [List.length_take_of_le (by omega),
      List.length_take_of_le (by
        have := hst.length_le
        omega)]

/-- The extended function preserves prefixes. -/
theorem stemExtension_prefix_mono {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    {s t : Node ι} (hst : s.IsPrefix t) :
    (stemExtensionFun hpos a A hA s).IsPrefix
      (stemExtensionFun hpos a A hA t) := by
  by_cases hs : s.length < n
  · by_cases ht : t.length < n
    · rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_lt hpos a A hA t ht]
      exact stemPreimage_prefix_mono a A hA hst
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_ge hpos a A hA t htge]
      have hp :
          (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)).IsPrefix
            (stemPreimage a A hA (stemTopPrefix n hpos t)) :=
        stemPreimage_prefix_mono a A hA
          (prefix_stemTopPrefix_of_prefix hpos hst hs)
      exact hp.trans (List.prefix_append _ _)
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := hsge.trans hst.length_le
    rw [stemExtensionFun_of_ge hpos a A hA s hsge,
        stemExtensionFun_of_ge hpos a A hA t htge]
    have htop := stemTopPrefix_eq_of_prefix hpos hst hsge
    rw [htop]
    exact StrongEmbedding.prefix_append_left
      (stemPreimage a A hA (stemTopPrefix n hpos t))
      (hst.drop (n - 1))

/-- The extension has a common length on every source level. -/
theorem stemExtension_length_eq_of_length_eq {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : Node ι) (hst : s.length = t.length) :
    (stemExtensionFun hpos a A hA s).length =
      (stemExtensionFun hpos a A hA t).length := by
  by_cases hs : s.length < n
  · have ht : t.length < n := by simpa [hst] using hs
    rw [stemExtensionFun_of_lt hpos a A hA s hs,
        stemExtensionFun_of_lt hpos a A hA t ht]
    exact stemPreimage_length_eq_of_length_eq a A hA
      (⟨s, hs⟩ : FiniteNode ι n)
      (⟨t, ht⟩ : FiniteNode ι n) hst
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := by simpa [hst] using hsge
    rw [stemExtensionFun_of_ge hpos a A hA s hsge,
        stemExtensionFun_of_ge hpos a A hA t htge,
        List.length_append, List.length_append]
    have hp := stemPreimage_length_eq_of_length_eq a A hA
      (stemTopPrefix n hpos s) (stemTopPrefix n hpos t) (by
        rw [stemTopPrefix_length_of_ge n hpos s hsge,
            stemTopPrefix_length_of_ge n hpos t htge])
    rw [hp, List.length_drop, List.length_drop, hst]

/-- Source-level strict increase gives strict increase of target lengths. -/
theorem stemExtension_length_lt_of_length_lt {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : Node ι) (hst : s.length < t.length) :
    (stemExtensionFun hpos a A hA s).length <
      (stemExtensionFun hpos a A hA t).length := by
  by_cases hs : s.length < n
  · by_cases ht : t.length < n
    · rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_lt hpos a A hA t ht]
      exact stemPreimage_length_lt_of_length_lt a A hA
        (⟨s, hs⟩ : FiniteNode ι n)
        (⟨t, ht⟩ : FiniteNode ι n) hst
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_ge hpos a A hA t htge,
          List.length_append]
      have hsle : s.length ≤ n - 1 := by omega
      have hp := stemPreimage_length_le_of_length_le a A hA
        (⟨s, hs⟩ : FiniteNode ι n)
        (stemTopPrefix n hpos t) (by
          rw [stemTopPrefix_length_of_ge n hpos t htge]
          exact hsle)
      have hdrop : 0 < (t.drop (n - 1)).length := by
        rw [List.length_drop]
        omega
      omega
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htge : n ≤ t.length := hsge.trans hst.le
    rw [stemExtensionFun_of_ge hpos a A hA s hsge,
        stemExtensionFun_of_ge hpos a A hA t htge,
        List.length_append, List.length_append,
        List.length_drop, List.length_drop]
    have hp := stemPreimage_length_eq_of_length_eq a A hA
      (stemTopPrefix n hpos s) (stemTopPrefix n hpos t) (by
        rw [stemTopPrefix_length_of_ge n hpos s hsge,
            stemTopPrefix_length_of_ge n hpos t htge])
    omega

/-- Canonical level map of the extension. -/
noncomputable def stemExtensionLevels [Nonempty ι] {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (k : ℕ) : ℕ :=
  (stemExtensionFun hpos a A hA (rayNode (ι := ι) k)).length

theorem stemExtension_same_level [Nonempty ι] {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) :
    (stemExtensionFun hpos a A hA s).length =
      stemExtensionLevels hpos a A hA s.length := by
  exact stemExtension_length_eq_of_length_eq hpos a A hA s
    (rayNode (ι := ι) s.length) (by simp)

theorem stemExtensionLevels_strictMono [Nonempty ι] {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A) :
    StrictMono (stemExtensionLevels hpos a A hA) := by
  intro k l hkl
  exact stemExtension_length_lt_of_length_lt hpos a A hA
    (rayNode (ι := ι) k) (rayNode (ι := ι) l) (by
      simpa using hkl)


/-- Target-length comparison reflects source-level comparison. -/
theorem stemExtension_source_length_le_of_target_length_le {n : ℕ}
    (hpos : 0 < n) (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    {s t : Node ι}
    (h :
      (stemExtensionFun hpos a A hA s).length ≤
        (stemExtensionFun hpos a A hA t).length) :
    s.length ≤ t.length := by
  by_contra hnot
  have hts : t.length < s.length := lt_of_not_ge hnot
  exact (not_lt_of_ge h)
    (stemExtension_length_lt_of_length_lt hpos a A hA t s hts)

/-- The extension reflects prefixes. -/
theorem stemExtension_prefix_reflect {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    {s t : Node ι}
    (hst :
      (stemExtensionFun hpos a A hA s).IsPrefix
        (stemExtensionFun hpos a A hA t)) :
    s.IsPrefix t := by
  have hlen : s.length ≤ t.length :=
    stemExtension_source_length_le_of_target_length_le hpos a A hA
      hst.length_le
  by_cases ht : t.length < n
  · have hs : s.length < n := lt_of_le_of_lt hlen ht
    rw [stemExtensionFun_of_lt hpos a A hA s hs,
        stemExtensionFun_of_lt hpos a A hA t ht] at hst
    exact stemPreimage_prefix_reflect a A hA hst
  · have htge : n ≤ t.length := le_of_not_gt ht
    by_cases hs : s.length < n
    · rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_ge hpos a A hA t htge] at hst
      have hsle : s.length ≤ n - 1 := by omega
      have hbaseLen :
          (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)).length ≤
            (stemPreimage a A hA (stemTopPrefix n hpos t)).length :=
        stemPreimage_length_le_of_length_le a A hA
          (⟨s, hs⟩ : FiniteNode ι n)
          (stemTopPrefix n hpos t) (by
            rw [stemTopPrefix_length_of_ge n hpos t htge]
            exact hsle)
      have hbase :
          (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)).IsPrefix
            (stemPreimage a A hA (stemTopPrefix n hpos t)) :=
        (List.isPrefix_append_of_length hbaseLen).mp hst
      have hsource :
          s.IsPrefix (stemTopPrefix n hpos t).1 :=
        stemPreimage_prefix_reflect a A hA hbase
      exact hsource.trans (List.take_prefix _ _)
    · have hsge : n ≤ s.length := le_of_not_gt hs
      rw [stemExtensionFun_of_ge hpos a A hA s hsge,
          stemExtensionFun_of_ge hpos a A hA t htge] at hst
      let ps := stemPreimage a A hA (stemTopPrefix n hpos s)
      let pt := stemPreimage a A hA (stemTopPrefix n hpos t)
      have hpLen :
          ps.length = pt.length :=
        stemPreimage_length_eq_of_length_eq a A hA
          (stemTopPrefix n hpos s) (stemTopPrefix n hpos t) (by
            rw [stemTopPrefix_length_of_ge n hpos s hsge,
                stemTopPrefix_length_of_ge n hpos t htge])
      have hpToWhole :
          ps.IsPrefix (pt ++ t.drop (n - 1)) :=
        (List.prefix_append _ _).trans hst
      have hpPrefix : ps.IsPrefix pt :=
        (List.isPrefix_append_of_length hpLen.le).mp hpToWhole
      have hpEq : ps = pt :=
        hpPrefix.eq_of_length hpLen
      have hdrop :
          (s.drop (n - 1)).IsPrefix (t.drop (n - 1)) := by
        have hcancel :
            (pt ++ s.drop (n - 1)).IsPrefix
              (pt ++ t.drop (n - 1)) := by
          simpa [ps, pt, hpEq] using hst
        exact StrongEmbedding.prefix_cancel_left pt hcancel
      have htop :
          stemTopPrefix n hpos s = stemTopPrefix n hpos t := by
        apply stemPreimage_injective a A hA
        exact hpEq
      have htake :
          s.take (n - 1) = t.take (n - 1) :=
        congrArg Subtype.val htop
      rw [← List.take_append_drop (n - 1) s,
          ← List.take_append_drop (n - 1) t, htake]
      exact StrongEmbedding.prefix_append_left _ hdrop

/-- The extended node map is injective. -/
theorem stemExtension_injective {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A) :
    Function.Injective (stemExtensionFun hpos a A hA) := by
  intro s t hst
  have hstP :
      (stemExtensionFun hpos a A hA s).IsPrefix
        (stemExtensionFun hpos a A hA t) := by
    simpa [hst]
  have htsP :
      (stemExtensionFun hpos a A hA t).IsPrefix
        (stemExtensionFun hpos a A hA s) := by
    simpa [hst]
  have hs := stemExtension_prefix_reflect hpos a A hA hstP
  have ht := stemExtension_prefix_reflect hpos a A hA htsP
  exact hs.eq_of_length (le_antisymm hs.length_le ht.length_le)

/-- Beyond the finite stem, the extension sends an immediate source child
to the literal corresponding child of the extended node. -/
theorem stemExtension_child_eq_of_ge {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) (i : ι)
    (hchild : n ≤ (child s i).length) :
    child (stemExtensionFun hpos a A hA s) i =
      stemExtensionFun hpos a A hA (child s i) := by
  by_cases hs : s.length < n
  · have hslen : s.length = n - 1 := by
      simp [child] at hchild
      omega
    have htop :
        stemTopPrefix n hpos (child s i) =
          (⟨s, hs⟩ : FiniteNode ι n) := by
      apply Subtype.ext
      simp [stemTopPrefix, child, hslen]
    rw [stemExtensionFun_of_lt hpos a A hA s hs,
        stemExtensionFun_of_ge hpos a A hA (child s i) hchild,
        htop]
    simp [child, hslen, List.append_assoc]
  · have hsge : n ≤ s.length := le_of_not_gt hs
    have htop :
        stemTopPrefix n hpos s =
          stemTopPrefix n hpos (child s i) :=
      stemTopPrefix_eq_of_prefix hpos
        (List.prefix_append s [i]) hsge
    rw [stemExtensionFun_of_ge hpos a A hA s hsge,
        stemExtensionFun_of_ge hpos a A hA (child s i) hchild,
        ← htop]
    have hdrop :
        (child s i).drop (n - 1) =
          s.drop (n - 1) ++ [i] := by
      simpa [child] using
        (List.drop_append_of_le_length (l₂ := [i]) (by omega :
          n - 1 ≤ s.length))
    rw [hdrop]
    simp [child, List.append_assoc]

/-- The extended function satisfies the strong-branch condition. -/
theorem stemExtension_branch {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : Node ι) (i : ι) :
    (child (stemExtensionFun hpos a A hA s) i).IsPrefix
      (stemExtensionFun hpos a A hA (child s i)) := by
  by_cases hchild : (child s i).length < n
  · have hs : s.length < n := by
      simp [child] at hchild ⊢
      omega
    rw [stemExtensionFun_of_lt hpos a A hA s hs,
        stemExtensionFun_of_lt hpos a A hA (child s i) hchild]
    exact stemPreimage_branch a A hA
      (⟨s, hs⟩ : FiniteNode ι n) i hchild
  · have hge : n ≤ (child s i).length := le_of_not_gt hchild
    have heq :=
      stemExtension_child_eq_of_ge hpos a A hA s i hge
    simpa only [heq]

/-- The extended function reflects the strong branch label. -/
theorem stemExtension_branch_reflect {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : Node ι) (i : ι)
    (h :
      (child (stemExtensionFun hpos a A hA s) i).IsPrefix
        (stemExtensionFun hpos a A hA t)) :
    (child s i).IsPrefix t := by
  by_cases hchild : (child s i).length < n
  · have hs : s.length < n := by
      simp [child] at hchild ⊢
      omega
    by_cases ht : t.length < n
    · rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_lt hpos a A hA t ht] at h
      exact stemPreimage_branch_reflect a A hA
        (⟨s, hs⟩ : FiniteNode ι n)
        (⟨t, ht⟩ : FiniteNode ι n) i h
    · have htge : n ≤ t.length := le_of_not_gt ht
      rw [stemExtensionFun_of_lt hpos a A hA s hs,
          stemExtensionFun_of_ge hpos a A hA t htge] at h
      let cs : FiniteNode ι n := ⟨child s i, hchild⟩
      let top := stemTopPrefix n hpos t
      have hbranch :
          (child (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)) i).IsPrefix
            (stemPreimage a A hA cs) :=
        stemPreimage_branch a A hA
          (⟨s, hs⟩ : FiniteNode ι n) i hchild
      have hsourceLen : cs.1.length ≤ top.1.length := by
        dsimp [cs, top]
        rw [stemTopPrefix_length_of_ge n hpos t htge]
        simp [child] at hchild ⊢
        omega
      have hstemLen :
          (stemPreimage a A hA cs).length ≤
            (stemPreimage a A hA top).length :=
        stemPreimage_length_le_of_length_le a A hA cs top hsourceLen
      have hleftLen :
          (child (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)) i).length ≤
            (stemPreimage a A hA top).length :=
        hbranch.length_le.trans hstemLen
      have hbase :
          (child (stemPreimage a A hA
              (⟨s, hs⟩ : FiniteNode ι n)) i).IsPrefix
            (stemPreimage a A hA top) :=
        (List.isPrefix_append_of_length hleftLen).mp h
      have hfinite :
          (child s i).IsPrefix top.1 :=
        stemPreimage_branch_reflect a A hA
          (⟨s, hs⟩ : FiniteNode ι n) top i hbase
      exact hfinite.trans (List.take_prefix _ _)
  · have hge : n ≤ (child s i).length := le_of_not_gt hchild
    have h' :
        (stemExtensionFun hpos a A hA (child s i)).IsPrefix
          (stemExtensionFun hpos a A hA t) := by
      rw [← stemExtension_child_eq_of_ge hpos a A hA s i hge]
      exact h
    exact stemExtension_prefix_reflect hpos a A hA h'

/-- Extend a finite pulled-back stem to an infinite strong embedding. -/
noncomputable def stemExtension [Nonempty ι] {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A) :
    StrongEmbedding ι where
  toFun := stemExtensionFun hpos a A hA
  injective := stemExtension_injective hpos a A hA
  prefix_mono := stemExtension_prefix_mono hpos a A hA
  prefix_reflect := stemExtension_prefix_reflect hpos a A hA
  branch := stemExtension_branch hpos a A hA
  branch_reflect := stemExtension_branch_reflect hpos a A hA
  level_witness :=
    ⟨stemExtensionLevels hpos a A hA,
      stemExtensionLevels_strictMono hpos a A hA,
      stemExtension_same_level hpos a A hA⟩

theorem stemExtension_agrees [Nonempty ι] {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : FiniteNode ι n) :
    (stemExtension hpos a A hA).toFun s.1 =
      stemPreimage a A hA s :=
  stemExtensionFun_of_lt hpos a A hA s.1 s.2

/-- Composing the target subtree with its pulled-back stem extension realizes
the prescribed finite approximation. -/
theorem approx_comp_stemExtension [Nonempty ι] {n : ℕ} (hpos : 0 < n)
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A) :
    approx ι n (StrongEmbedding.comp A (stemExtension hpos a A hA)) = a := by
  apply Subtype.ext
  funext s
  change A.toFun ((stemExtension hpos a A hA).toFun s.1) = a.1 s
  rw [stemExtension_agrees hpos a A hA s,
      stemPreimage_spec a A hA s]

end StrongTreeSpace
end Milliken
