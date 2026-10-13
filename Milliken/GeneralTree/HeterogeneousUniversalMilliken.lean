import Milliken.GeneralTree.HeterogeneousWedgeComplementTransfer
import Milliken.GeneralTree.HeterogeneousReducedInduction
import Milliken.GeneralTree.HeterogeneousFiniteStrongHL

/-!
# Universal heterogeneous HDHL and arbitrary-tree Milliken: final induction

This is the proof architecture of Todorčević §3 and Chapter 6,
using the checked homogeneous/general-tree ingredients already present
in lean-milliken:

* dimension-one HDHL is unconditional;
* Remark 3.8 selects source levels whose complement has no restricted
  somewhere-dense matrix;
* a full (not thinned) compression of each factor is installed as
  the actual strong-cone component of one common-root wedge ambient;
* checked matrix and obstruction transport converts that negative
  hypothesis into the ordinary one on the synchronized wedge;
* the checked reduced dimension induction gives a dense positive
  matrix in the wedge;
* transport back gives the required original highly-dense statement.

The dimension induction is deliberately **universal over the ambient
tree**: at each stage it must apply the previous-dimensional theorem
to the newly constructed wedge rather than silently treating each
coordinate compression as a strong subtree of its old ambient.

Once universal heterogeneous HDHL is proved, the existing checked
finite-colour product HL, boundary A.4, Abstract Ellentuck and
original 1979 finite-tree conversions immediately give Milliken.
-/

namespace Milliken
namespace GeneralTree

open CompressedSourceSelection
open HeterogeneousCompressionWedge

variable {U : AmbientTree} {d : ℕ}

/-- Exact selected-source-level reduced dichotomy, assuming only
the universally available previous-dimensional HDHL statement.
The new wedge ambient is allowed to be different from the input U. -/
theorem heterogeneousRestrictedReduced_of_previous_universal
    (P : Fin (d + 1) → StrongSubtree U)
    (hd : 0 < d)
    (f : CompressedSourceSelection)
    (hAll : ∀ (V : AmbientTree) (S : Fin d → StrongSubtree V),
      HasHeterogeneousHDHL S) :
    HeterogeneousRestrictedReducedDichotomy P f.indices := by
  classical
  intro Q hno
  let hdim : 0 < d + 1 := Nat.zero_lt_succ d
  let V : AmbientTree := ambient P f hdim
  let R : Fin (d + 1) → StrongSubtree V := strong P f hdim
  have hR : ∀ i, (R i).levels = (fun n : ℕ => n + 1) :=
    strong_levels P f hdim
  have hprev :
      ∀ S : Fin d → StrongSubtree V, HasHeterogeneousHDHL S :=
    hAll V
  have hnoW :
      ¬ HeterogeneousContainsSomewhereDense
        R (liftedColour P f hdim Q)ᶜ :=
    no_wedge_complement_somewhereDense P f hdim Q hno
  obtain ⟨N, hNdense, hNcolour⟩ :=
    heterogeneousReducedHDHL_of_previous
      R hd (fun n : ℕ => n + 1) hR hprev
      (liftedColour P f hdim Q) hnoW
  let M : HeterogeneousCompressedMatrix P f :=
    decodeMatrix P f hdim N
  refine ⟨M.original, ?_, ?_⟩
  · exact decodeMatrix_original_denseAt
      P f hdim N 1 hNdense
  · exact decodeMatrix_original_subset
      P f hdim N Q hNcolour

/-- HDHL in dimension d+1, simultaneously for all ambient trees
and all finite families of their strong subtrees. No global degree
bound or fixed branching alphabet is assumed. -/
theorem universalHeterogeneousHDHL :
    ∀ (n : ℕ) (V : AmbientTree)
      (P : Fin (n + 1) → StrongSubtree V),
      HasHeterogeneousHDHL P := by
  intro n
  induction n with
  | zero =>
      intro V P
      exact heterogeneousHDHL_one P
  | succ n ih =>
      intro V P
      apply heterogeneousHDHL_of_restrictedReduced P
      intro Q hQ k
      let f : CompressedSourceSelection := {
        indices := heterogeneousRemark38Levels P hQ k
        zero := heterogeneousRemark38Levels_zero P hQ k
        strictMono :=
          heterogeneousRemark38Levels_strictMono P hQ k
      }
      have hAll :
          ∀ (W : AmbientTree)
            (S : Fin (n + 1) → StrongSubtree W),
            HasHeterogeneousHDHL S :=
        fun W S => ih W S
      exact heterogeneousRestrictedReduced_of_previous_universal
        P (Nat.zero_lt_succ n) f hAll

/-- The unconditional heterogeneous highly-dense Halpern–Läuchli
theorem for every positive finite dimension of arbitrary pruned,
locally finitely branching strong-tree products. -/
theorem heterogeneousHDHL_unconditional
    (d : ℕ) (hd : 0 < d)
    (V : AmbientTree) (P : Fin d → StrongSubtree V) :
    HasHeterogeneousHDHL P := by
  cases d with
  | zero =>
      omega
  | succ n =>
      exact universalHeterogeneousHDHL n V P

/-- Todorčević's topological Milliken theorem for arbitrary
pruned, locally finite ambient trees, with no heterogeneous
HL or HDHL hypothesis remaining. -/
theorem generalMilliken_unconditional
    (V : AmbientTree) :
    RamseySpace.IsTopologicalRamseySpaceTextbook
      (S := generalApproximationSystem V) :=
  generalMilliken_of_all_heterogeneousHDHL V
    (fun d P hd => heterogeneousHDHL_unconditional d hd V P)

/-- The original finite-colour Milliken 1979 theorem for every
pruned, locally finite ambient rooted tree, now unconditional. -/
theorem milliken1979_general_unconditional
    (V : AmbientTree) :
    HasMillikenFiniteColourProperty V :=
  milliken1979_of_all_heterogeneousHDHL V
    (fun d P hd => heterogeneousHDHL_unconditional d hd V P)

end GeneralTree
end Milliken
