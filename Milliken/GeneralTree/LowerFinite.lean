import Milliken.GeneralTree.FiniteOrder
import Mathlib.Data.Set.Card

/-!
# A.2 lower-cone finiteness for arbitrary locally finitely branching trees

A height-n realised strong finite subtree has n nonempty selected levels
at distinct ambient ranks. If its nodes all lie in a finite set B,
choosing one node per source level gives an injection from Fin n to B.
Thus n ≤ B.ncard. Combining this uniform height bound with the proved
fixed-height finiteness yields the full lower-finiteness clause A.2(1)
for Todorčević's book-facing order (6.3).

There is no degree bound on the ambient tree or the finite approximations.
The remaining A.2 clauses (realization of the infinite refinement order
and prefix compatibility) are separate obligations.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- If the carrier of a height-n finite strong subtree is inside a finite
set B, its n distinct nonempty selected source levels give n distinct
nodes of B. -/
theorem height_le_ncard_of_subset {n : ℕ}
    (a : SFinite U n) {B : Set U}
    (hB : B.Finite) (hsub : a.carrier ⊆ B) :
    n ≤ B.ncard := by
  classical
  letI : Finite B := hB.to_subtype
  letI : Fintype B := Fintype.ofFinite _
  obtain ⟨S, hSa⟩ := a.realised
  let choose : Fin n → B := fun i =>
    ⟨Classical.choose (S.sourceLevel_nonempty i), by
      have hi := Classical.choose_spec (S.sourceLevel_nonempty i)
      apply hsub
      rw [hSa]
      exact ⟨hi.1, i, i.isLt, hi.2⟩⟩
  have hlevel (i : Fin n) :
      U.level (choose i).1 = S.levels i :=
    (Classical.choose_spec (S.sourceLevel_nonempty i)).2
  have hinj : Function.Injective choose := by
    intro i j hij
    have hl : S.levels i = S.levels j := by
      calc
        S.levels i = U.level (choose i).1 := (hlevel i).symm
        _ = U.level (choose j).1 :=
          congrArg (U.level) (congrArg Subtype.val hij)
        _ = S.levels j := hlevel j
    exact Fin.ext (S.levels_strictMono.injective hl)
  have hcard := Fintype.card_le_of_injective choose hinj
  simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard] using hcard

/-- A.2(1): every finite approximation has only finitely many
predecessors under the literal published finitization (6.3). -/
theorem bookLeFin_lowerFinite
    (b : Σ m, SFinite U m) :
    {a : Σ n, SFinite U n | bookLeFin a b}.Finite := by
  classical
  let B : Set U := b.2.carrier
  have hB : B.Finite := b.2.carrier_finite
  let N : ℕ := B.ncard
  let Bounded :=
    Σ i : Fin (N + 1),
      {a : SFinite U i.1 // a.carrier ⊆ B}
  letI : ∀ i : Fin (N + 1),
      Finite {a : SFinite U i.1 // a.carrier ⊆ B} :=
    fun i => (boundedApprox_finite (U := U) hB i.1).to_subtype
  letI : Finite Bounded := inferInstance
  let forget : Bounded → (Σ n, SFinite U n) :=
    fun q => ⟨q.1.1, q.2.1⟩
  apply (Set.finite_range forget).subset
  intro a ha
  have hsub : a.2.carrier ⊆ B := (bookLeFin_iff.mp ha).1
  have hn : a.1 ≤ N :=
    height_le_ncard_of_subset a.2 hB hsub
  let i : Fin (N + 1) := ⟨a.1, Nat.lt_succ_of_le hn⟩
  let q : Bounded := ⟨i, ⟨a.2, hsub⟩⟩
  exact ⟨q, rfl⟩

end GeneralTree
end Milliken
