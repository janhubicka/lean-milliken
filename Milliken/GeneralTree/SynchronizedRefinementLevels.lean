import Milliken.GeneralTree.OrderRealization

/-!
# Synchronized strong refinements preserve monochromatic level products

If the input coordinate strong trees share an ambient selected-level map,
and a family of strong refinements also shares one map, then each
source-level product of the refinements lies inside a *single*
source-level product of the inputs.

This elementary alignment is needed when applying a binary
Halpern--Läuchli theorem repeatedly to eliminate finitely many
colours. It prevents a subtle error: coordinatewise refinement alone
does not say that every coordinate is refined at the same source
index. Equality of the selected ambient level maps supplies precisely
the required synchronization.

No branching bound, HL statement, or Ramsey assumption appears.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Any synchronized strong-refinement product level is contained
in one common source-level product of the larger coordinate trees. -/
theorem synchronizedRefinement_sourceLevel
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (LP LR : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = LP)
    (hR : ∀ i, (R i).levels = LR)
    (hRP : ∀ i, (R i).Refines (P i))
    (k : ℕ) :
    ∃ j : ℕ,
      ∀ i, (R i).sourceLevel k ⊆ (P i).sourceLevel j := by
  let i0 : Fin d := ⟨0, hd⟩
  obtain ⟨j, hj⟩ :=
    (R i0).selectedLevel_of_refines (hRP i0) k
  refine ⟨j, ?_⟩
  intro i z hz
  refine ⟨hRP i hz.1, ?_⟩
  calc
    U.level z = (R i).levels k := hz.2
    _ = LR k := congrFun (hR i) k
    _ = (R i0).levels k := (congrFun (hR i0) k).symm
    _ = (P i0).levels j := hj
    _ = LP j := congrFun (hP i0) j
    _ = (P i).levels j := (congrFun (hP i) j).symm

/-- A colour constant on every common level product of P stays
constant on every common level product of a synchronized refinement. -/
theorem synchronizedRefinement_preserves_homogeneity
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (LP LR : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = LP)
    (hR : ∀ i, (R i).levels = LR)
    (hRP : ∀ i, (R i).Refines (P i))
    {α : Type}
    (colour : (Fin d → U) → α)
    (a : α)
    (hmono : ∀ k (x : Fin d → U),
      (∀ i, x i ∈ (P i).sourceLevel k) → colour x = a) :
    ∀ k (x : Fin d → U),
      (∀ i, x i ∈ (R i).sourceLevel k) → colour x = a := by
  intro k x hx
  obtain ⟨j, hj⟩ :=
    synchronizedRefinement_sourceLevel P R hd LP LR hP hR hRP k
  apply hmono j x
  intro i
  exact hj i (hx i)

end GeneralTree
end Milliken
