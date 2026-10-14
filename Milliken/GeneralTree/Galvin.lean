import Milliken.GeneralTree.HeterogeneousUniversalMilliken
import Milliken.GeneralTree.Original1979Conditional

/-!
# Todorčević Corollary 6.7: Galvin's avoidance/hitting alternative

Let F be any family of finite strong-tree approximations. There is
an infinite strong T such that either none of the F-approximations
is contained in T, or every infinite strong subtree of T has a finite
initial approximation in F.

The proof is a direct application of the *topological*, not merely
fixed-height finite-colour, Milliken theorem. The set of infinite
trees having some initial approximation in F is Ellentuck-open:
one witnessed prefix already determines an entire basic neighbourhood.

The present theorem is stated for the library's realised `FiniteApprox`
objects. An additional intrinsic-finite equivalence (under development
in `GeneralTree.IntrinsicFinite`) is needed to restate it literally
for all intrinsic finite strong trees of the book.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- A strong infinite tree meets a family of finite approximations
if it has *some initial segment* in the family. -/
def HasFamilyInitialPart (F : Set (Σ n, SFinite U n))
    (T : StrongSubtree U) : Prop :=
  ∃ n : ℕ, (⟨n, r n T⟩ : Σ n, SFinite U n) ∈ F

/-- Being met by a finite initial part is open in the literal
Ellentuck topology. The family may include approximations of
arbitrarily large heights, so this is not just a fixed-k colour fibre. -/
theorem isOpen_hasFamilyInitialPart
    (F : Set (Σ n, SFinite U n)) :
    (generalApproximationSystem U).IsEllentuckOpen
      {T | HasFamilyInitialPart F T} := by
  intro T hT
  obtain ⟨n, hn⟩ := hT
  refine ⟨n, r n T, T,
    ⟨StrongSubtree.refines_refl T, rfl⟩, ?_⟩
  intro Y hY
  refine ⟨n, ?_⟩
  have hprefix : r n Y = r n T := hY.2
  rw [hprefix]
  exact hn

/-- The realised-approximation form of Todorčević, Corollary 6.7.
For any family of finite strong-tree pictures, some infinite strong
tree either avoids every picture or forces every further strong
subtree to have an initial segment belonging to that family.

No restriction on F (such as fixed height or Borel complexity) is made.
The proof uses the full Baire-set theorem for an **open** set and the
checked relative finite-prefix extension lemma. -/
theorem galvinAlternative_realized
    (U : AmbientTree) (F : Set (Σ n, SFinite U n)) :
    ∃ T : StrongSubtree U,
      (∀ a : Σ n, SFinite U n,
          a ∈ F → ¬ a.2.carrier ⊆ T.carrier) ∨
      (∀ S : StrongSubtree U,
          S.Refines T → HasFamilyInitialPart F S) := by
  classical
  let R := generalApproximationSystem U
  let target : Set (StrongSubtree U) :=
    {S | HasFamilyInitialPart F S}
  letI : TopologicalSpace R.Point := R.ellentuckTopology
  have hopen : @IsOpen R.Point R.ellentuckTopology target :=
    (R.isOpen_ellentuck_iff target).2
      (isOpen_hasFamilyInitialPart F)
  have hBaire :
      @BaireMeasurableSet R.Point R.ellentuckTopology target :=
    hopen.baireMeasurableSet
  have hRamsey :
      RamseySpace.IsRamseyOnBasicNeighborhoods (S := R) target :=
    (generalMilliken_unconditional U).1 target hBaire
  let I : StrongSubtree U := identityStrongSubtree U
  have hne : (R.neighborhood (r 0 I) I).Nonempty :=
    ⟨I, StrongSubtree.refines_refl I, rfl⟩
  obtain ⟨T, hTI, hhom⟩ :=
    hRamsey (r 0 I) I hne
  refine ⟨T, ?_⟩
  rcases hhom with hsub | hdis
  · right
    intro S hST
    apply hsub
    exact ⟨hST, r_zero_eq S I⟩
  · left
    intro a ha hcontain
    obtain ⟨S, hST, hSa⟩ :=
      exists_refinement_realising_general a.2 T hcontain
    have hS : S ∈ R.neighborhood (r 0 I) T :=
      ⟨hST, r_zero_eq S I⟩
    have hHit : S ∈ target := by
      change HasFamilyInitialPart F S
      refine ⟨a.1, ?_⟩
      simpa only [hSa] using ha
    exact (Set.disjoint_left.mp hdis) hS hHit

end GeneralTree
end Milliken
