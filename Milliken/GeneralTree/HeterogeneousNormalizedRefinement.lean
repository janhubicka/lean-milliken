import Milliken.GeneralTree.HeterogeneousTailNormalization

/-!
# One corrected normalized refinement step in heterogeneous Lemma 3.15

Fix a front-coordinate source-level-k base tuple and a level matrix A
which is dense above it at an original scale n0 and avoids a finite
family of last-coordinate sections. Given a new avoiding level
matrix at a scale n above A's support, first tail-normalize the new
witness, then refine it over A.

The resulting matrix preserves the original density and all old
section avoidance by stabilization, avoids the new section by
inclusion into the later matrix, and lies on a strictly later
common selected source level. This is the actual-tree analogue
of the nested refinement step hidden in equation (3)
of Todorčević's Lemma 3.15.

No fixed alphabet, global branching bound, HDHL or HL assumption
occurs in the proof; only explicit section stabilization is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The support level of a nonempty cone-dense level matrix must
lie on or after its density test source index. -/
theorem heterogeneous_support_ge_of_onLevel_denseAbove
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    {k n l : ℕ}
    (base : HeterogeneousLevelTuple P k)
    (hkn : k ≤ n)
    (M : HeterogeneousMatrix P)
    (hOn : M.OnLevel l)
    (hDense : M.DenseAbove base.1 n) :
    n ≤ l := by
  let i0 : Fin d := ⟨0, hd⟩
  obtain ⟨v, hv, hbv⟩ :=
    (P i0).exists_sourceLevel_descendant hkn (base.2 i0)
  obtain ⟨w, hw, hvw⟩ :=
    hDense i0 v hv hbv
  have hle : (P i0).levels n ≤ (P i0).levels l := by
    calc
      (P i0).levels n = U.level v := hv.2.symm
      _ ≤ U.level w := U.level_mono hvw
      _ = (P i0).levels l := (hOn i0 w hw).2
  by_contra hbad
  have hlt : l < n := Nat.lt_of_not_ge hbad
  have hrank := (P i0).levels_strictMono hlt
  omega

/-- Corrected heterogeneous matrix-refinement step:
adding a new avoided section preserves the old cone density
and every previous avoided section, under stabilization. -/
theorem heterogeneousNormalizedRefinementStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    {k n0 n lA : ℕ}
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (A : HeterogeneousMatrix
      (fun i : Fin d => P i.castSucc))
    (Y : Set U)
    (hAlevel : A.OnLevel lA)
    (hAdense : A.DenseAbove base.1 n0)
    (hAabove : ∀ z ∈ A.carrier, ∀ i, base.1 i ≤ z i)
    (hAavoid : ∀ y ∈ Y,
      A.carrier ⊆
        (heterogeneousLastSection
          (heterogeneousTailNormalize P Q) y)ᶜ)
    (hYbelow : ∀ y ∈ Y, ∃ t : ℕ,
      y ∈ (P (Fin.last d)).sourceLevel t ∧ t < lA)
    (hlAn : lA < n)
    (hkn : k < n)
    {t : ℕ} (y : U)
    (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (hnew : HeterogeneousSectionAvoidAt P
      (heterogeneousTailNormalize P Q) y base.1 n) :
    ∃ C : HeterogeneousMatrix
        (fun i : Fin d => P i.castSucc),
      ∃ lC : ℕ,
        C.OnLevel lC ∧
        C.DenseAbove base.1 n0 ∧
        (∀ z ∈ C.carrier, ∀ i, base.1 i ≤ z i) ∧
        (∀ z ∈ Set.insert y Y,
          C.carrier ⊆
            (heterogeneousLastSection
              (heterogeneousTailNormalize P Q) z)ᶜ) ∧
        (∀ z ∈ Set.insert y Y,
          ∃ s : ℕ,
            z ∈ (P (Fin.last d)).sourceLevel s ∧ s < lC) ∧
        lA < lC := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  obtain ⟨B, lB, hBlevel, hBdense, hBavoid,
    _hBabove, hyB⟩ :=
    heterogeneousSectionAvoid_normalized_support_gt
      P Q hd base hkn y hy hnew
  have hnB : n ≤ lB :=
    heterogeneous_support_ge_of_onLevel_denseAbove
      Front hd base (Nat.le_of_lt hkn) B hBlevel hBdense
  have hlAB : lA < lB := hlAn.trans_le hnB
  let C : HeterogeneousMatrix Front := A.refineOver B
  have hClevel : C.OnLevel lB :=
    HeterogeneousMatrix.refineOver_onLevel hBlevel
  have hBDenseA : B.DenseAbove base.1 lA :=
    B.denseAbove_of_le base.1 (Nat.le_of_lt hlAn) hBdense
  have hCdense : C.DenseAbove base.1 n0 :=
    HeterogeneousMatrix.refineOver_denseAbove
      hAlevel hAdense hBDenseA
  have hCabove :
      ∀ z ∈ C.carrier, ∀ i, base.1 i ≤ z i := by
    intro z hz i
    obtain ⟨a, haA, haz⟩ :=
      HeterogeneousMatrix.exists_predecessor_of_mem_refineOver hz
    exact (hAabove a haA i).trans (haz i)
  have hstabNorm :
      HeterogeneousStabilized P
        (heterogeneousTailNormalize P Q) :=
    heterogeneousStabilized_tailNormalize P Q hd hstab
  have hCold :
      ∀ z ∈ Y, C.carrier ⊆
        (heterogeneousLastSection
          (heterogeneousTailNormalize P Q) z)ᶜ := by
    intro z hz
    obtain ⟨s, hzs, hsA⟩ := hYbelow z hz
    exact HeterogeneousMatrix.refineOver_avoids_section
      P (heterogeneousTailNormalize P Q)
      hstabNorm hd z hzs hAlevel hBlevel
      hsA (hAavoid z hz)
  have hCnew : C.carrier ⊆
      (heterogeneousLastSection
        (heterogeneousTailNormalize P Q) y)ᶜ :=
    (HeterogeneousMatrix.refineOver_carrier_subset_right A B).trans
      hBavoid
  have hCall :
      ∀ z ∈ Set.insert y Y, C.carrier ⊆
        (heterogeneousLastSection
          (heterogeneousTailNormalize P Q) z)ᶜ := by
    intro z hz
    rcases hz with rfl | hzOld
    · exact hCnew
    · exact hCold z hzOld
  have hBelow :
      ∀ z ∈ Set.insert y Y, ∃ s : ℕ,
        z ∈ (P (Fin.last d)).sourceLevel s ∧ s < lB := by
    intro z hz
    rcases hz with rfl | hzOld
    · exact ⟨t, hy, hyB⟩
    · obtain ⟨s, hzs, hsA⟩ := hYbelow z hzOld
      exact ⟨s, hzs, hsA.trans hlAB⟩
  exact ⟨C, lB, hClevel, hCdense, hCabove,
    hCall, hBelow, hlAB⟩

end GeneralTree
end Milliken
