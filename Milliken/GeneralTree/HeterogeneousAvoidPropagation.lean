import Milliken.GeneralTree.HeterogeneousBadSections
import Milliken.GeneralTree.SpliceCones

/-!
# Propagation of an avoiding section to every later level vector

This is the source-faithful heterogeneous analogue of equation (3)
in Todorčević's Lemma 3.15. Suppose a level matrix avoids the
last-coordinate section at y while remaining n-dense in the
descendant cones of a selected level-k tuple.

For any later level vector extending this tuple, truncate to
source index n and use cone density to choose matrix entries
above the truncations. Source ancestors of the chosen matrix
entries and the later vector agree at the earlier index t+1,
where t is the selected source index of y. Stabilization (*)
therefore transfers section membership from the later vector
to the avoiding matrix, a contradiction.

The proof works in genuinely heterogeneous input trees and uses
neither word alphabets nor uniform branching bounds.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- An avoiding matrix above a finite base tuple excludes all
later front-coordinate vectors extending that tuple, provided
the last-coordinate section obeys the source-level stabilization
property (*). -/
theorem heterogeneousSectionAvoidAt_propagates
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hstab : HeterogeneousStabilized P Q)
    (hd : 0 < d)
    {t k n l : ℕ}
    (y : U) (hy : y ∈ (P (Fin.last d)).sourceLevel t)
    (base : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k)
    (hkn : k < n) (htn : t < n)
    (hAvoid : HeterogeneousSectionAvoidAt P Q y base.1 n)
    (z : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) l)
    (hnl : n ≤ l)
    (hbasez : ∀ i, base.1 i ≤ z.1 i) :
    z.1 ∉ heterogeneousLastSection Q y := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  obtain ⟨M, L, hOn, hDense, hAvoidM⟩ := hAvoid
  let u : HeterogeneousLevelTuple Front n :=
    heterogeneousTruncate Front hnl z
  have huz (i : Fin d) : u.1 i ≤ z.1 i :=
    heterogeneousTruncate_le Front hnl z i
  have hbu (i : Fin d) : base.1 i ≤ u.1 i := by
    have hrank : U.level (base.1 i) ≤ U.level (u.1 i) := by
      calc
        U.level (base.1 i) = (Front i).levels k :=
          (base.2 i).2
        _ ≤ (Front i).levels n :=
          (Front i).levels_strictMono.monotone
            (Nat.le_of_lt hkn)
        _ = U.level (u.1 i) := (u.2 i).2.symm
    exact U.le_of_common_descendant_of_level_le
      (hbasez i) (huz i) hrank
  let witness : ∀ i : Fin d,
      ∃ w : U, w ∈ M.coord i ∧ u.1 i ≤ w :=
    fun i => hDense i (u.1 i) (u.2 i) (hbu i)
  let w : Fin d → U := fun i => Classical.choose (witness i)
  have hw (i : Fin d) :
      w i ∈ M.coord i ∧ u.1 i ≤ w i :=
    Classical.choose_spec (witness i)
  have hwCarrier : w ∈ M.carrier := fun i => (hw i).1
  have hwLevel (i : Fin d) :
      w i ∈ (Front i).sourceLevel L :=
    hOn i (w i) (hw i).1
  let i0 : Fin d := ⟨0, hd⟩
  have hnL : n ≤ L := by
    have hle : (Front i0).levels n ≤
        (Front i0).levels L := by
      calc
        (Front i0).levels n = U.level (u.1 i0) :=
          (u.2 i0).2.symm
        _ ≤ U.level (w i0) := U.level_mono (hw i0).2
        _ = (Front i0).levels L := (hwLevel i0).2
    by_contra hbad
    have hLn : L < n := Nat.lt_of_not_ge hbad
    have hlt := (Front i0).levels_strictMono hLn
    omega
  have htL : t < L := htn.trans_le hnL
  have htl : t < l := htn.trans_le hnl
  have hqN : t + 1 ≤ n := Nat.succ_le_of_lt htn
  let wv : HeterogeneousLevelTuple Front L := ⟨w, hwLevel⟩
  have hWu :
      heterogeneousTruncate Front
        (Nat.succ_le_of_lt htL) wv =
        heterogeneousTruncate Front hqN u := by
    have hEq := heterogeneousTruncate_eq_of_le
      Front hqN hnL u wv (fun i => (hw i).2)
    exact hEq.symm
  have hZu :
      heterogeneousTruncate Front
        (Nat.succ_le_of_lt htl) z =
        heterogeneousTruncate Front hqN u := by
    have hEq := heterogeneousTruncate_eq_of_le
      Front hqN hnl u z huz
    exact hEq.symm
  intro hzSection
  have hZtrunc :
      (heterogeneousTruncate Front
        (Nat.succ_le_of_lt htl) z).1 ∈
        heterogeneousLastSection Q y :=
    (hstab t l y hy z htl).mp hzSection
  have hSame :
      heterogeneousTruncate Front
        (Nat.succ_le_of_lt htL) wv =
      heterogeneousTruncate Front
        (Nat.succ_le_of_lt htl) z :=
    hWu.trans hZu.symm
  have hWtrunc :
      (heterogeneousTruncate Front
        (Nat.succ_le_of_lt htL) wv).1 ∈
        heterogeneousLastSection Q y := by
    rw [hSame]
    exact hZtrunc
  have hWsection : wv.1 ∈ heterogeneousLastSection Q y :=
    (hstab t L y hy wv htL).mpr hWtrunc
  exact hAvoidM hwCarrier hWsection

end GeneralTree
end Milliken
