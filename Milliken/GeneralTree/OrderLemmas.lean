import Milliken.GeneralTree.SourceLevels

/-!
# Elementary approximation and finitisation laws for arbitrary rooted trees

These are the source-faithful A.1/A.2 preliminaries for the space
of infinite strong subtrees of an arbitrary locally finitely branching
pruned ambient tree.

The main A.1 coherence/separation lemmas and the A.2/A.3/A.4 structures
for general U are not claimed here. In particular, this file does not
deduce Milliken's theorem for arbitrary U.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace StrongSubtree

theorem refines_refl (S : StrongSubtree U) : S.Refines S :=
  fun _ hx => hx

theorem refines_trans {S T R : StrongSubtree U}
    (hST : S.Refines T) (hTR : T.Refines R) :
    S.Refines R :=
  hST.trans hTR

end StrongSubtree

namespace FiniteApprox

/-- A finite approximation has no extra data beyond its carrier:
realisation witnesses are proofs and hence proof-irrelevant. -/
theorem ext_carrier {n : ℕ} {a b : FiniteApprox U n}
    (h : a.carrier = b.carrier) : a = b := by
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      cases h
      rfl

end FiniteApprox

/-- A.1 surjectivity: all finite approximations in this data model
come from infinite strong subtrees, by their realisation witness. -/
theorem r_surjective (n : ℕ) :
    Function.Surjective (r (U := U) n) := by
  intro a
  obtain ⟨S, hS⟩ := a.realised
  refine ⟨S, ?_⟩
  apply FiniteApprox.ext_carrier
  exact hS.symm

/-- All infinite strong trees have the same empty approximation. -/
theorem r_zero_eq (S T : SInfinity U) :
    r 0 S = r 0 T := by
  apply FiniteApprox.ext_carrier
  simp only [r_zero_carrier]

/-- Formula (6.1) for the successor restriction. -/
theorem r_succ_carrier (S : SInfinity U) (n : ℕ) :
    (r (n + 1) S).carrier =
      S.initialPart n ∪ S.sourceLevel n :=
  StrongSubtree.initialPart_succ S n

/-- Basic neighbourhood inclusion under strong refinement. -/
theorem basicNeighborhood_mono
    {n : ℕ} (a : SFinite U n) {S T : SInfinity U}
    (hST : S.Refines T) :
    BasicNeighborhood a S ⊆ BasicNeighborhood a T := by
  rintro X ⟨hXS, hXa⟩
  exact ⟨hXS.trans hST, hXa⟩

/-- Nested basic neighbourhoods can be composed. -/
theorem basicNeighborhood_trans
    {n : ℕ} (a : SFinite U n) {S T : SInfinity U}
    (hST : S ∈ BasicNeighborhood a T) :
    BasicNeighborhood a S ⊆ BasicNeighborhood a T :=
  basicNeighborhood_mono a hST.1

/-- The redundant empty-empty disjunct of (6.3) is absorbed by
the carrier / maximal-level inclusion clause. -/
theorem bookLeFin_iff {a b : Σ n, SFinite U n} :
    bookLeFin a b ↔
      a.2.carrier ⊆ b.2.carrier ∧
        maxLevel a.2 ⊆ maxLevel b.2 := by
  constructor
  · intro h
    rcases h with ⟨ha, hb⟩ | hab
    · constructor
      · intro x hx
        rw [ha] at hx
        simp at hx
      · intro x hx
        have hcarrier : x ∈ a.2.carrier :=
          maxLevel_subset_carrier a.2 hx
        rw [ha] at hcarrier
        simp at hcarrier
    · exact hab
  · exact Or.inr

/-- The published finitisation (6.3) is transitive. -/
theorem bookLeFin_trans {a b c : Σ n, SFinite U n}
    (hab : bookLeFin a b) (hbc : bookLeFin b c) :
    bookLeFin a c := by
  obtain ⟨hab₁, hab₂⟩ := (bookLeFin_iff.mp hab)
  obtain ⟨hbc₁, hbc₂⟩ := (bookLeFin_iff.mp hbc)
  apply bookLeFin_iff.mpr
  exact ⟨hab₁.trans hbc₁, hab₂.trans hbc₂⟩

end GeneralTree
end Milliken
