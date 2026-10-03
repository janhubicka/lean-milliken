import Milliken.FinitizationOrder

/-!
# Finite stems inside a strong subtree

This is the finite pullback used in A.3 and later in the proof of A.4.
If the carrier of a realized finite approximation `a` lies in the range
of a strong embedding `A`, every node of `a` has a unique preimage in
`A`.  Those preimages form a finite strong stem.

The next file extends such a stem to an infinite strong embedding.  Keeping
the finite pullback separate makes the grafting argument in Chapter 6
reusable.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- Pull a finite approximation back through a strong subtree containing
its carrier. -/
noncomputable def stemPreimage {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : FiniteNode ι n) : Node ι :=
  Classical.choose (hA ⟨s, rfl⟩)

theorem stemPreimage_spec {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : FiniteNode ι n) :
    A.toFun (stemPreimage a A hA s) = a.1 s :=
  Classical.choose_spec (hA ⟨s, rfl⟩)

theorem stemPreimage_eq_realizer {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : FiniteNode ι n) :
    A.toFun (stemPreimage a A hA s) =
      (approxRealizer a).toFun s.1 := by
  rw [stemPreimage_spec, approxRealizer_spec]

theorem stemPreimage_injective {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A) :
    Function.Injective (stemPreimage a A hA) := by
  intro s t hst
  apply Subtype.ext
  apply (approxRealizer a).injective
  rw [← stemPreimage_eq_realizer a A hA s,
      ← stemPreimage_eq_realizer a A hA t, hst]

theorem stemPreimage_prefix_mono {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    {s t : FiniteNode ι n} (hst : s.1.IsPrefix t.1) :
    (stemPreimage a A hA s).IsPrefix
      (stemPreimage a A hA t) := by
  apply A.prefix_reflect
  rw [stemPreimage_eq_realizer a A hA s,
      stemPreimage_eq_realizer a A hA t]
  exact (approxRealizer a).prefix_mono hst

theorem stemPreimage_prefix_reflect {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    {s t : FiniteNode ι n}
    (hst :
      (stemPreimage a A hA s).IsPrefix
        (stemPreimage a A hA t)) :
    s.1.IsPrefix t.1 := by
  apply (approxRealizer a).prefix_reflect
  rw [← stemPreimage_eq_realizer a A hA s,
      ← stemPreimage_eq_realizer a A hA t]
  exact A.prefix_mono hst

theorem stemPreimage_branch {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s : FiniteNode ι n) (i : ι)
    (hchild : (child s.1 i).length < n) :
    (child (stemPreimage a A hA s) i).IsPrefix
      (stemPreimage a A hA
        (⟨child s.1 i, hchild⟩ : FiniteNode ι n)) := by
  apply A.branch_reflect
  rw [stemPreimage_eq_realizer a A hA s,
      stemPreimage_eq_realizer a A hA
        (⟨child s.1 i, hchild⟩ : FiniteNode ι n)]
  exact (approxRealizer a).branch s.1 i

theorem stemPreimage_branch_reflect {n : ℕ} (a : Approx ι n)
    (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : FiniteNode ι n) (i : ι)
    (h :
      (child (stemPreimage a A hA s) i).IsPrefix
        (stemPreimage a A hA t)) :
    (child s.1 i).IsPrefix t.1 := by
  apply (approxRealizer a).branch_reflect s.1 t.1 i
  rw [← stemPreimage_eq_realizer a A hA s,
      ← stemPreimage_eq_realizer a A hA t]
  exact (A.branch (stemPreimage a A hA s) i).trans
    (A.prefix_mono h)

/-- Pulled-back nodes on one source level have one common length. -/
theorem stemPreimage_length_eq_of_length_eq {n : ℕ}
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : FiniteNode ι n) (hst : s.1.length = t.1.length) :
    (stemPreimage a A hA s).length =
      (stemPreimage a A hA t).length := by
  rcases A.level_witness with ⟨alev, haMono, haLev⟩
  rcases (approxRealizer a).level_witness with
    ⟨rlev, hrMono, hrLev⟩
  have hs := congrArg List.length
    (stemPreimage_eq_realizer a A hA s)
  have ht := congrArg List.length
    (stemPreimage_eq_realizer a A hA t)
  rw [haLev, hrLev] at hs ht
  apply haMono.injective
  calc
    alev (stemPreimage a A hA s).length
        = rlev s.1.length := hs
    _ = rlev t.1.length := congrArg rlev hst
    _ = alev (stemPreimage a A hA t).length := ht.symm

/-- Pulled-back stem levels are strictly increasing. -/
theorem stemPreimage_length_lt_of_length_lt {n : ℕ}
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : FiniteNode ι n) (hst : s.1.length < t.1.length) :
    (stemPreimage a A hA s).length <
      (stemPreimage a A hA t).length := by
  rcases A.level_witness with ⟨alev, haMono, haLev⟩
  rcases (approxRealizer a).level_witness with
    ⟨rlev, hrMono, hrLev⟩
  have hs := congrArg List.length
    (stemPreimage_eq_realizer a A hA s)
  have ht := congrArg List.length
    (stemPreimage_eq_realizer a A hA t)
  rw [haLev, hrLev] at hs ht
  apply haMono.lt_iff_lt.mp
  rw [hs, ht]
  exact hrMono hst

theorem stemPreimage_length_le_of_length_le {n : ℕ}
    (a : Approx ι n) (A : StrongEmbedding ι)
    (hA : approxCarrier a ⊆ StrongEmbedding.range A)
    (s t : FiniteNode ι n) (hst : s.1.length ≤ t.1.length) :
    (stemPreimage a A hA s).length ≤
      (stemPreimage a A hA t).length := by
  rcases hst.eq_or_lt with h | h
  · exact (stemPreimage_length_eq_of_length_eq a A hA s t h).le
  · exact (stemPreimage_length_lt_of_length_lt a A hA s t h).le

end StrongTreeSpace
end Milliken
