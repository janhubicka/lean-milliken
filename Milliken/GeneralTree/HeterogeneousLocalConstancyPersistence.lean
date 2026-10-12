import Milliken.GeneralTree.HeterogeneousLocalStabilization
import Milliken.GeneralTree.HeterogeneousCommonIndex

/-!
# Preservation of local heterogeneous section constancy

The finite stabilization fusion repeatedly refines synchronized
strong-tree factors, often replacing source-n boundary nodes by
deeper descendants. A constancy condition established at one
old source-n boundary tuple must therefore survive after the
boundary tuple itself changes.

The common source-index map f shows that all coordinates of
a new source-level product are simultaneously on one older
source level f(k). An old cone-constancy condition may then be
applied at f(n) to the new base and at f(l) to every subsequent
tuple. The resulting equivalences have the same old base,
and hence compose.

This is a pure inheritance lemma: no HL theorem, additional
branching assumption, colour choice, or axiom is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Cone constancy survives synchronized strong refinements when
the new selected boundary tuple descends coordinatewise from the
old selected boundary tuple, even if the selected source levels
change and the replacement boundary nodes lie much deeper. -/
theorem HeterogeneousConeConstant.refinement
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (hR : ∀ i, (R i).levels = M)
    (hRP : ∀ i, (R i).Refines (P i))
    (A : Set (Fin d → U))
    {n : ℕ}
    (b : HeterogeneousLevelTuple P n)
    (hconst : HeterogeneousConeConstant P A b)
    (b' : HeterogeneousLevelTuple R n)
    (hbb' : ∀ i, b.1 i ≤ b'.1 i) :
    HeterogeneousConeConstant R A b' := by
  classical
  obtain ⟨f, hf, _, hsub⟩ :=
    exists_synchronizedRefinement_commonIndex
      P R hd L M hP hR hRP
  let i0 : Fin d := ⟨0, hd⟩
  have hbf : b'.1 i0 ∈ (P i0).sourceLevel (f n) :=
    hsub n i0 (b'.2 i0)
  have hn : n ≤ f n := by
    have hlev : (P i0).levels n ≤ (P i0).levels (f n) := by
      calc
        (P i0).levels n = U.level (b.1 i0) :=
          (b.2 i0).2.symm
        _ ≤ U.level (b'.1 i0) := U.level_mono (hbb' i0)
        _ = (P i0).levels (f n) := hbf.2
    by_contra hnot
    have hfn : f n < n := Nat.lt_of_not_ge hnot
    have hstrict := (P i0).levels_strictMono hfn
    omega
  let pb : HeterogeneousLevelTuple P (f n) :=
    ⟨b'.1, fun i => hsub n i (b'.2 i)⟩
  have hbConst :
      b'.1 ∈ A ↔ b.1 ∈ A :=
    hconst (f n) pb hn hbb'
  intro l z hnl hb'z
  have hfl : n ≤ f l :=
    hn.trans (hf.monotone hnl)
  let pz : HeterogeneousLevelTuple P (f l) :=
    ⟨z.1, fun i => hsub l i (z.2 i)⟩
  have hbz : ∀ i, b.1 i ≤ z.1 i := by
    intro i
    exact (hbb' i).trans (hb'z i)
  have hzConst :
      z.1 ∈ A ↔ b.1 ∈ A :=
    hconst (f l) pz hfl hbz
  exact hzConst.trans hbConst.symm

end GeneralTree
end Milliken
