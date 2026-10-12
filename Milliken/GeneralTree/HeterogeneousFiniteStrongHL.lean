import Milliken.GeneralTree.HeterogeneousBinaryStrongHL
import Milliken.GeneralTree.SynchronizedRefinementLevels
import Milliken.GeneralTree.BoundaryMilliken
import Milliken.GeneralTree.Original1979Conditional

/-!
# Finite-color general-tree HL from all-dimensional heterogeneous HDHL

Binary heterogeneous strong-subtree HL has been proved from HDHL in
the same dimension. This module reduces arbitrary positive finite
numbers of colours to that binary result by successive synchronized
strong refinements. The synchronization lemma is essential: an
arbitrary coordinatewise refinement might select different *source
indices* in different factors, whereas the recursive argument needs
one common previous level for the binary colour.

Thus the full general product HL, the published A.4, and both the
textbook topological and original 1979 Milliken conclusions follow
from exactly one explicitly visible remaining combinatorial premise:
heterogeneous HDHL for every positive finite dimension and every
finite family of arbitrary locally finite strong-tree factors.

No additional branching bound, HL axiom, or unproved convenience
lemma is introduced.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Binary HL for every synchronized family in a fixed dimension
suffices to eliminate any positive finite number of colours.
We use universal HDHL in this *fixed* dimension, so the induction
can call binary HL after each successive strong refinement. -/
theorem heterogeneousFiniteSynchronizedHL_of_all_hdhl
    (d : ℕ) (hd : 0 < d)
    (hAll : ∀ P : Fin d → StrongSubtree U, HasHeterogeneousHDHL P) :
    ∀ (n : ℕ) (P : Fin d → StrongSubtree U)
      (L : ℕ → ℕ)
      (hP : ∀ i, (P i).levels = L)
      (colour : (Fin d → U) → Fin (n + 1)),
      ∃ a : Fin (n + 1), ∃ M : ℕ → ℕ,
        ∃ F : Fin d → StrongSubtree U,
          StrictMono M ∧
          (∀ i, (F i).Refines (P i) ∧ (F i).levels = M) ∧
          ∀ k (x : Fin d → U),
            (∀ i, x i ∈ (F i).sourceLevel k) → colour x = a := by
  intro n
  induction n with
  | zero =>
      intro P L hP colour
      let i0 : Fin d := ⟨0, hd⟩
      have hL : StrictMono L := by
        rw [← hP i0]
        exact (P i0).levels_strictMono
      refine ⟨0, L, P, hL, ?_, ?_⟩
      · intro i
        exact ⟨StrongSubtree.refines_refl (P i), hP i⟩
      · intro k x hx
        exact Fin.eq_zero _
  | succ n ih =>
      intro P L hP colour
      let last : Fin (n + 2) := Fin.last (n + 1)
      let binary : (Fin d → U) → Fin 2 :=
        fun x => if colour x = last then 1 else 0
      obtain ⟨b, LB, F, hLB, hF, hBmono⟩ :=
        heterogeneousBinarySynchronizedHL_of_hdhl
          P hd (hAll P) L hP binary
      by_cases hb : b = (1 : Fin 2)
      · refine ⟨last, LB, F, hLB, hF, ?_⟩
        intro k x hx
        have hbin : binary x = (1 : Fin 2) := by
          exact (hBmono k x hx).trans hb
        by_contra hnot
        have hzero : binary x = (0 : Fin 2) := by
          simp [binary, hnot]
        exact (by decide : (0 : Fin 2) ≠ 1)
          (hzero.symm.trans hbin)
      · have hb0 : b = (0 : Fin 2) := by
          apply Fin.ext
          have hlt : b.val < 2 := b.isLt
          have hne : b.val ≠ 1 := by
            intro heq
            apply hb
            apply Fin.ext
            simpa using heq
          omega
        let reduced : (Fin d → U) → Fin (n + 1) :=
          fun x =>
            if h : colour x = last then
              0
            else
              ⟨(colour x).val, by
                have hlt := (colour x).isLt
                have hne : (colour x).val ≠ n + 1 := by
                  intro hv
                  apply h
                  apply Fin.ext
                  simpa [last] using hv
                omega⟩
        obtain ⟨a, LG, G, hLG, hG, hRed⟩ :=
          ih F LB (fun i => (hF i).2) reduced
        have hGF : ∀ i, (G i).Refines (F i) :=
          fun i => (hG i).1
        refine ⟨a.castSucc, LG, G, hLG, ?_, ?_⟩
        · intro i
          exact ⟨(hGF i).trans (hF i).1, (hG i).2⟩
        · intro k x hxG
          obtain ⟨j, hj⟩ :=
            synchronizedRefinement_sourceLevel
              F G hd LB LG
              (fun i => (hF i).2)
              (fun i => (hG i).2)
              hGF k
          have hxF : ∀ i, x i ∈ (F i).sourceLevel j := by
            intro i
            exact hj i (hxG i)
          have hnotLast : colour x ≠ last := by
            intro hlast
            have hbin : binary x = (0 : Fin 2) :=
              (hBmono j x hxF).trans hb0
            have hone : binary x = (1 : Fin 2) := by
              simp [binary, hlast]
            exact (by decide : (1 : Fin 2) ≠ 0)
              (hone.symm.trans hbin)
          have hred : reduced x = a :=
            hRed k x hxG
          have hcast : (reduced x).castSucc = colour x := by
            apply Fin.ext
            simp [reduced, hnotLast]
          exact hcast.symm.trans (congrArg Fin.castSucc hred)

/-- The exact multi-dimensional, finite-colour product
Halpern--Läuchli interface required by general-tree A.4 follows
from universally available heterogeneous HDHL. The latter
is an explicit *unproved premise*, not a Lean axiom. -/
theorem generalProductHL_of_all_heterogeneousHDHL
    (U : AmbientTree)
    (hAll : ∀ (d : ℕ) (P : Fin d → StrongSubtree U),
      0 < d → HasHeterogeneousHDHL P) :
    HasGeneralProductHL U := by
  classical
  intro d colors hcolors P L hP colour
  cases d with
  | zero =>
      let F : Fin 0 → StrongSubtree U := fun i => Fin.elim0 i
      let emptyTuple : Fin 0 → U := fun i => Fin.elim0 i
      refine ⟨colour emptyTuple, (fun n => n), F,
        strictMono_id, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro k x hx
        have heq : x = emptyTuple := by
          funext i
          exact Fin.elim0 i
        rw [heq]
  | succ d =>
      cases colors with
      | zero =>
          exact False.elim ((NeZero.ne (0 : ℕ)) rfl)
      | succ n =>
          have hd : 0 < d + 1 := Nat.zero_lt_succ d
          obtain ⟨a, M, F, hM, hF, hmono⟩ :=
            heterogeneousFiniteSynchronizedHL_of_all_hdhl
              (U := U) (d + 1) hd (fun R => hAll (d + 1) R hd)
              n P L hP colour
          exact ⟨a, M, F, hM, hF, hmono⟩

/-- No extra combinatorial statement beyond universal
heterogeneous HDHL is needed to discharge the published
boundary-instance Halpern--Läuchli hypothesis. -/
theorem boundaryProductHL_of_all_heterogeneousHDHL
    (U : AmbientTree)
    (hAll : ∀ (d : ℕ) (P : Fin d → StrongSubtree U),
      0 < d → HasHeterogeneousHDHL P) :
    HasBoundaryProductHL U :=
  boundaryProductHL_of_generalProductHL U
    (generalProductHL_of_all_heterogeneousHDHL U hAll)

/-- Topological Milliken for arbitrary pruned locally finite trees,
conditional solely on HDHL for the actual heterogeneous tree factors. -/
theorem generalMilliken_of_all_heterogeneousHDHL
    (U : AmbientTree)
    (hAll : ∀ (d : ℕ) (P : Fin d → StrongSubtree U),
      0 < d → HasHeterogeneousHDHL P) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := generalApproximationSystem U) :=
  generalMilliken_of_boundaryProductHL U
    (boundaryProductHL_of_all_heterogeneousHDHL U hAll)

/-- Original finite-colour Milliken 1979, with the same one
explicit HDHL antecedent and no extra hidden Ramsey principle. -/
theorem milliken1979_of_all_heterogeneousHDHL
    (U : AmbientTree)
    (hAll : ∀ (d : ℕ) (P : Fin d → StrongSubtree U),
      0 < d → HasHeterogeneousHDHL P) :
    HasMillikenFiniteColourProperty U :=
  milliken1979_of_boundaryProductHL U
    (boundaryProductHL_of_all_heterogeneousHDHL U hAll)

end GeneralTree
end Milliken
