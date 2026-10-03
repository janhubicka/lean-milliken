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

end StrongTreeSpace
end Milliken
