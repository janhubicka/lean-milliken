import Milliken.GeneralTree.HeterogeneousBadSections

/-!
# Tail normalization for the heterogeneous HDHL induction

The stabilization property (*) compares source truncations only when
the front-coordinate source level is strictly later than the source
index of the fixed last-coordinate node y. In the book's Lemma 3.15
an avoiding level matrix is implicitly assumed to have support later
than y; the checked homogeneous formalization makes this true by
enlarging the colour class on low-level tuples.

We use exactly that normalization for arbitrary pruned locally
finitely branching input strong trees. A tuple is declared to belong
to the normalized colour class if every front coordinate belongs
to some selected source level no later than y's selected index.

On a common front level above y, the normalized section is unchanged.
The complement shrinks, stabilization is retained, and any
cone-dense level-supported matrix avoiding a normalized section
is forced to have support strictly later than y.

No fixed ambient alphabet, uniform degree bound, or unproved HL
assumption is used in these statements.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Enlarge Q on tuples whose front coordinates lie at source
indices no later than the selected source index of their last node. -/
def heterogeneousTailNormalize
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) :
    Set (Fin (d + 1) → U) :=
  {z | z ∈ Q ∨
    ∃ t : ℕ,
      heteroLast z ∈ (P (Fin.last d)).sourceLevel t ∧
        ∀ i : Fin d, ∃ k : ℕ, k ≤ t ∧
          z i.castSucc ∈ (P i.castSucc).sourceLevel k}

/-- Normalization on a front/last tuple has the exact
selected-source-index meaning intended above. -/
@[simp] theorem mem_heterogeneousTailNormalize_appendLast
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (x : Fin d → U) (y : U) :
    heteroAppendLast x y ∈ heterogeneousTailNormalize P Q ↔
      heteroAppendLast x y ∈ Q ∨
        ∃ t : ℕ,
          y ∈ (P (Fin.last d)).sourceLevel t ∧
            ∀ i : Fin d, ∃ k : ℕ, k ≤ t ∧
              x i ∈ (P i.castSucc).sourceLevel k := by
  simp [heterogeneousTailNormalize, heteroLast, heteroAppendLast]

/-- On any front source level strictly above the source index
of y, the normalized last-coordinate section equals the old
section, using one front coordinate to rule out the low case. -/
theorem heterogeneousTailNormalize_section_of_above
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    {t l : ℕ} (y : U)
    (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) l)
    (htl : t < l) :
    x.1 ∈ heterogeneousLastSection
      (heterogeneousTailNormalize P Q) y ↔
    x.1 ∈ heterogeneousLastSection Q y := by
  change
    heteroAppendLast x.1 y ∈ heterogeneousTailNormalize P Q ↔
      heteroAppendLast x.1 y ∈ Q
  rw [mem_heterogeneousTailNormalize_appendLast]
  constructor
  · intro h
    rcases h with hQ | ⟨s, hys, hlow⟩
    · exact hQ
    · have hst : s = t :=
        (P (Fin.last d)).levels_strictMono.injective
          (hys.2.symm.trans hy.2)
      let i0 : Fin d := ⟨0, hd⟩
      obtain ⟨k, hks, hxk⟩ := hlow i0
      have hkl : k = l :=
        (P i0.castSucc).levels_strictMono.injective
          (hxk.2.symm.trans (x.2 i0).2)
      omega
  · exact Or.inl

/-- At any front source level no later than y, every
tuple is automatically in the normalized section. -/
theorem heterogeneousTailNormalize_section_of_le
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    {t l : ℕ} (y : U)
    (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) l)
    (hlt : l ≤ t) :
    x.1 ∈ heterogeneousLastSection
      (heterogeneousTailNormalize P Q) y := by
  change heteroAppendLast x.1 y ∈ heterogeneousTailNormalize P Q
  rw [mem_heterogeneousTailNormalize_appendLast]
  right
  exact ⟨t, hy, fun i => ⟨l, hlt, x.2 i⟩⟩

/-- Stabilization is unchanged under tail normalization
in every positive front dimension. -/
theorem heterogeneousStabilized_tailNormalize
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q) :
    HeterogeneousStabilized P
      (heterogeneousTailNormalize P Q) := by
  intro t l y hy x htl
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  let q := t + 1
  have hq : q ≤ l := Nat.succ_le_of_lt htl
  have hhigh :=
    heterogeneousTailNormalize_section_of_above
      P Q hd y hy x htl
  have htrunc :=
    heterogeneousTailNormalize_section_of_above
      P Q hd y hy
      (heterogeneousTruncate Front hq x)
      (Nat.lt_succ_self t)
  exact hhigh.trans ((hstab t l y hy x htl).trans htrunc.symm)

/-- The normalization contains Q. -/
theorem subset_heterogeneousTailNormalize
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) :
    Q ⊆ heterogeneousTailNormalize P Q :=
  fun _ h => Or.inl h

/-- Its complement is included in the original complement. -/
theorem heterogeneousTailNormalize_compl_subset
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U)) :
    (heterogeneousTailNormalize P Q)ᶜ ⊆ Qᶜ := by
  intro z hz hQ
  exact hz (subset_heterogeneousTailNormalize P Q hQ)

/-- A cone-dense level matrix avoiding a normalized section
must have support strictly later than y's selected source index.
Otherwise a chosen matrix vector would automatically belong to
the normalized section. -/
theorem heterogeneousSectionAvoid_normalized_support_gt
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    {k n t : ℕ}
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (hkn : k < n)
    (y : U) (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (hAvoid : HeterogeneousSectionAvoidAt P
      (heterogeneousTailNormalize P Q) y base.1 n) :
    ∃ M : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc),
      ∃ L : ℕ,
        M.OnLevel L ∧ M.DenseAbove base.1 n ∧
        M.carrier ⊆
          (heterogeneousLastSection
            (heterogeneousTailNormalize P Q) y)ᶜ ∧
        (∀ z ∈ M.carrier, ∀ i, base.1 i ≤ z i) ∧
        t < L := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  obtain ⟨A, L, hOn, hDense, hAvoidA⟩ := hAvoid
  let N := A.restrictAbove base.1
  have hNOn : N.OnLevel L := by
    intro i z hz
    exact hOn i z hz.1
  have hNDense : N.DenseAbove base.1 n := by
    intro i z hz hbase
    obtain ⟨w, hwA, hzw⟩ := hDense i z hz hbase
    exact ⟨w, ⟨hwA, hbase.trans hzw⟩, hzw⟩
  have hNAvoid : N.carrier ⊆
      (heterogeneousLastSection
        (heterogeneousTailNormalize P Q) y)ᶜ :=
    (A.restrictAbove_carrier_subset base.1).trans hAvoidA
  have hNbase :
      ∀ z ∈ N.carrier, ∀ i, base.1 i ≤ z i := by
    intro z hz i
    exact (hz i).2
  have htL : t < L := by
    by_contra hbad
    have hLt : L ≤ t := Nat.le_of_not_gt hbad
    let unode : Fin d → U :=
      fun i => Classical.choose
        ((Front i).exists_sourceLevel_descendant
          (Nat.le_of_lt hkn) (base.2 i))
    have hu (i : Fin d) :
        unode i ∈ (Front i).sourceLevel n ∧
          base.1 i ≤ unode i :=
      Classical.choose_spec
        ((Front i).exists_sourceLevel_descendant
          (Nat.le_of_lt hkn) (base.2 i))
    let witness : ∀ i : Fin d,
        ∃ z : U, z ∈ A.coord i ∧ unode i ≤ z :=
      fun i => hDense i (unode i) (hu i).1 (hu i).2
    let w : Fin d → U :=
      fun i => Classical.choose (witness i)
    have hw (i : Fin d) :
        w i ∈ A.coord i ∧ unode i ≤ w i :=
      Classical.choose_spec (witness i)
    have hwCarrier : w ∈ A.carrier :=
      fun i => (hw i).1
    let wvec : HeterogeneousLevelTuple Front L :=
      ⟨w, fun i => hOn i (w i) (hw i).1⟩
    have hwLow :
        wvec.1 ∈ heterogeneousLastSection
          (heterogeneousTailNormalize P Q) y :=
      heterogeneousTailNormalize_section_of_le
        P Q y hy wvec hLt
    exact hAvoidA hwCarrier hwLow
  exact ⟨N, L, hNOn, hNDense,
    hNAvoid, hNbase, htL⟩

end GeneralTree
end Milliken
