import Milliken.Factor
import RamseySpace.Closed

/-!
# Closedness of the strong-subtree approximation space

A coherent full approximation code determines a unique strong embedding by
reading a source node `s` from the approximation of height
`s.length + 1`.  Prefix realizability lets every finite verification be
performed inside one genuine strong embedding.

This is the Chapter 6 analogue of the closedness proof for the classical
Ellentuck space in `lean-ramsey-space-todorcevic`.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- Read the image of one source node from a full approximation code. -/
def codeValue (c : (S ι).ApproximationCode) (s : Node ι) : Node ι :=
  (c (s.length + 1)).1 ⟨s, Nat.lt_succ_self _⟩

theorem codeValue_eq_of_realizer
    (c : (S ι).ApproximationCode)
    (X : StrongEmbedding ι) (s : Node ι)
    (hX : approx ι (s.length + 1) X = c (s.length + 1)) :
    codeValue c s = X.toFun s := by
  have h := congrArg
    (fun a : Approx ι (s.length + 1) =>
      a.1 (⟨s, Nat.lt_succ_self _⟩ : FiniteNode ι (s.length + 1)))
    hX
  exact h.symm

/-- Realize enough of a code to cover two specified source nodes. -/
theorem exists_realizer_pair
    (c : (S ι).ApproximationCode)
    (h : ∀ N, (S ι).PrefixRealizable c N)
    (s t : Node ι) :
    ∃ X : StrongEmbedding ι,
      codeValue c s = X.toFun s ∧
      codeValue c t = X.toFun t := by
  let N := max (s.length + 1) (t.length + 1)
  rcases h N with ⟨X, hX⟩
  refine ⟨X, ?_, ?_⟩
  · exact codeValue_eq_of_realizer c X s
      (hX (s.length + 1) (Nat.le_max_left _ _))
  · exact codeValue_eq_of_realizer c X t
      (hX (t.length + 1) (Nat.le_max_right _ _))

/-- The level map read from a code, using the canonical ray only to choose
one representative source node from each level. -/
noncomputable def codeLevels [Nonempty ι]
    (c : (S ι).ApproximationCode) (n : ℕ) : ℕ :=
  (codeValue c (rayNode (ι := ι) n)).length

theorem codeValue_same_level [Nonempty ι]
    (c : (S ι).ApproximationCode)
    (h : ∀ N, (S ι).PrefixRealizable c N)
    (s : Node ι) :
    (codeValue c s).length = codeLevels c s.length := by
  rcases exists_realizer_pair c h s (rayNode (ι := ι) s.length) with
    ⟨X, hs, hr⟩
  rcases X.level_witness with ⟨lev, hlev, hXlev⟩
  rw [hs, hr, hXlev, hXlev, rayNode_length]
  rfl

theorem codeLevels_strictMono [Nonempty ι]
    (c : (S ι).ApproximationCode)
    (h : ∀ N, (S ι).PrefixRealizable c N) :
    StrictMono (codeLevels c) := by
  intro n m hnm
  rcases exists_realizer_pair c h
      (rayNode (ι := ι) n) (rayNode (ι := ι) m) with
    ⟨X, hn, hm⟩
  rcases X.level_witness with ⟨lev, hlev, hXlev⟩
  change (codeValue c (rayNode (ι := ι) n)).length <
    (codeValue c (rayNode (ι := ι) m)).length
  rw [hn, hm, hXlev, hXlev, rayNode_length, rayNode_length]
  exact hlev hnm

/-- A prefix-realizable code determines a strong embedding. -/
noncomputable def pointOfCode [Nonempty ι]
    (c : (S ι).ApproximationCode)
    (h : ∀ N, (S ι).PrefixRealizable c N) :
    StrongEmbedding ι where
  toFun := codeValue c
  injective := by
    intro s t hst
    rcases exists_realizer_pair c h s t with ⟨X, hs, ht⟩
    apply X.injective
    rw [← hs, ← ht, hst]
  prefix_mono := by
    intro s t hst
    rcases exists_realizer_pair c h s t with ⟨X, hs, ht⟩
    rw [hs, ht]
    exact X.prefix_mono hst
  prefix_reflect := by
    intro s t hst
    rcases exists_realizer_pair c h s t with ⟨X, hs, ht⟩
    apply X.prefix_reflect
    rw [← hs, ← ht]
    exact hst
  branch := by
    intro s i
    rcases exists_realizer_pair c h s (child s i) with ⟨X, hs, ht⟩
    rw [hs, ht]
    exact X.branch s i
  branch_reflect := by
    intro s t i hst
    rcases exists_realizer_pair c h s t with ⟨X, hs, ht⟩
    apply X.branch_reflect s t i
    rw [← hs, ← ht]
    exact hst
  level_witness := by
    exact ⟨codeLevels c, codeLevels_strictMono c h,
      codeValue_same_level c h⟩

theorem approx_pointOfCode [Nonempty ι]
    (c : (S ι).ApproximationCode)
    (h : ∀ N, (S ι).PrefixRealizable c N)
    (n : ℕ) :
    approx ι n (pointOfCode c h) = c n := by
  rcases h n with ⟨X, hX⟩
  apply Subtype.ext
  funext s
  have hsCode :
      codeValue c s.1 = X.toFun s.1 :=
    codeValue_eq_of_realizer c X s.1
      (hX (s.1.length + 1) (by omega))
  have hsN := congrArg
    (fun a : Approx ι n => a.1 s)
    (hX n le_rfl)
  change codeValue c s.1 = (c n).1 s
  exact hsCode.trans hsN

/-- The strong-subtree approximation image is closed in the product /
first-difference topology. -/
theorem isMetricallyClosed [Nonempty ι] :
    (S ι).IsMetricallyClosed := by
  intro c h
  refine ⟨pointOfCode c h, ?_⟩
  intro n
  exact approx_pointOfCode c h n

end StrongTreeSpace
end Milliken
