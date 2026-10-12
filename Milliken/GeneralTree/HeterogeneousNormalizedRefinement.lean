import Milliken.GeneralTree.HeterogeneousTailNormalization

/-!
# Normalized matrix refinement for heterogeneous HDHL

This is the finite recursive refinement step in the proof of
Todorčević's Lemma 3.15, stated for actual non-isomorphic,
node-dependently finitely branching strong trees.

The previous matrix avoids finitely many stabilized last-coordinate
sections.  A new high-density avoiding witness is trimmed to its
base cone and refined over the old matrix.  The resulting matrix
retains the old cone density, avoids all old and new sections,
and has a strictly higher source-level support.

The only inputs are an explicitly stabilized colour class and
the new section-avoidance witness.  No heterogeneous HL axiom
or uniform bound on the branching degrees is assumed.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A level-supported matrix dense above a source-level-k base at
a later index n must be supported at source index at least n.
The positive-dimension requirement is essential. -/
theorem HeterogeneousMatrix.support_ge_of_onLevel_denseAbove
    {P : Fin d → StrongSubtree U}
    (M : HeterogeneousMatrix P) {k n l : ℕ}
    (hd : 0 < d)
    (base : HeterogeneousLevelTuple P k)
    (hkn : k < n)
    (hon : M.OnLevel l)
    (hdense : M.DenseAbove base.1 n) :
    n ≤ l := by
  let i0 : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx, hbasex⟩ :=
    (P i0).exists_sourceLevel_descendant
      (Nat.le_of_lt hkn) (base.2 i0)
  obtain ⟨z, hz, hxz⟩ := hdense i0 x hx hbasex
  have hle : (P i0).levels n ≤ (P i0).levels l := by
    calc
      (P i0).levels n = U.level x := hx.2.symm
      _ ≤ U.level z := U.level_mono hxz
      _ = (P i0).levels l := (hon i0 z hz).2
  by_contra hnot
  have hlt : l < n := Nat.lt_of_not_ge hnot
  have hstrict := (P i0).levels_strictMono hlt
  omega

/-- One source-faithful step of the corrected heterogeneous
Lemma 3.15 avoidance construction.  Each previously processed last
node comes equipped with its genuine selected source index; the
resulting matrix support lies strictly beyond all of these indices. -/
theorem heterogeneousNormalized_refinement_step
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
    (hAbase : ∀ z ∈ A.carrier, ∀ i, base.1 i ≤ z i)
    (hAavoid : ∀ z ∈ Y,
      A.carrier ⊆ (heterogeneousLastSection
        (heterogeneousTailNormalize P Q) z)ᶜ)
    (hYbelow : ∀ z ∈ Y,
      ∃ t, z ∈ (P (Fin.last d)).sourceLevel t ∧ t < lA)
    (hlAn : lA < n)
    (hkn : k < n)
    (y : U) (t : ℕ)
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
          C.carrier ⊆ (heterogeneousLastSection
            (heterogeneousTailNormalize P Q) z)ᶜ) ∧
        (∀ z ∈ Set.insert y Y,
          ∃ q, z ∈ (P (Fin.last d)).sourceLevel q ∧ q < lC) ∧
        lA < lC := by
  classical
  obtain ⟨B, lB, hBlevel, hBdense, hBavoid, _, htyB⟩ :=
    heterogeneousSectionAvoid_normalized_support_gt
      P Q hd base hkn y hy hnew
  have hnB : n ≤ lB :=
    B.support_ge_of_onLevel_denseAbove hd base hkn hBlevel hBdense
  have hlAB : lA < lB := hlAn.trans_le hnB
  let C := A.refineOver B
  have hClevel : C.OnLevel lB :=
    HeterogeneousMatrix.refineOver_onLevel hBlevel
  have hCdense : C.DenseAbove base.1 n0 := by
    apply HeterogeneousMatrix.refineOver_denseAbove hAlevel hAdense
    exact B.denseAbove_of_le base.1 (Nat.le_of_lt hlAn) hBdense
  have hCbase :
      ∀ z ∈ C.carrier, ∀ i, base.1 i ≤ z i := by
    intro z hz i
    obtain ⟨a, ha, haz⟩ :=
      HeterogeneousMatrix.exists_predecessor_of_mem_refineOver hz
    exact (hAbase a ha i).trans (haz i)
  have hstabN : HeterogeneousStabilized P
      (heterogeneousTailNormalize P Q) :=
    heterogeneousStabilized_tailNormalize P Q hd hstab
  have hCavoid :
      ∀ z ∈ Set.insert y Y,
        C.carrier ⊆ (heterogeneousLastSection
          (heterogeneousTailNormalize P Q) z)ᶜ := by
    intro z hz
    rcases hz with rfl | hzY
    · exact (HeterogeneousMatrix.refineOver_carrier_subset_right A B).trans
        hBavoid
    · obtain ⟨q, hzq, hqA⟩ := hYbelow z hzY
      exact HeterogeneousMatrix.refineOver_avoids_section
        P (heterogeneousTailNormalize P Q) hstabN hd
        z hzq hAlevel hBlevel hqA (hAavoid z hzY)
  have hCbelow :
      ∀ z ∈ Set.insert y Y,
        ∃ q, z ∈ (P (Fin.last d)).sourceLevel q ∧ q < lB := by
    intro z hz
    rcases hz with rfl | hzY
    · exact ⟨t, hy, htyB⟩
    · obtain ⟨q, hzq, hqA⟩ := hYbelow z hzY
      exact ⟨q, hzq, hqA.trans hlAB⟩
  exact ⟨C, lB, hClevel, hCdense, hCbase, hCavoid, hCbelow, hlAB⟩

end GeneralTree
end Milliken
