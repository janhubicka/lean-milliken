import Milliken.GeneralTree.SynchronizedRefinementLevels
import Milliken.GeneralTree.HeterogeneousHDHLBase
import Milliken.GeneralTree.BoundaryCones

/-!
# A single source-index map for synchronized strong refinements

Suppose all coordinate input trees have one selected ambient-level
map L and all coordinate refinements have a second such map M.
Coordinatewise refinement alone initially gives a possibly different
source-level index in each input tree. Equality of the ambient heights
and strict monotonicity of L show that these indices necessarily agree.

This supplies a *single strictly increasing source-index map* f such
that M(k) = L(f(k)) and every refined source level k is contained in
the input source level f(k), simultaneously in all coordinates.

We also specialize the result to the family of cones at an actual
source-level boundary tuple. This is the index used when grafting
heterogeneous stabilization witnesses while preserving a finite stem.
No Halpern--Läuchli assumption or uniform branching degree is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Synchronized strong refinements admit one and the same
strictly increasing input source-index map. -/
theorem exists_synchronizedRefinement_commonIndex
    (P R : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (LP LR : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = LP)
    (hR : ∀ i, (R i).levels = LR)
    (hRP : ∀ i, (R i).Refines (P i)) :
    ∃ f : ℕ → ℕ,
      StrictMono f ∧
      (∀ k, LR k = LP (f k)) ∧
      (∀ k i, (R i).sourceLevel k ⊆
        (P i).sourceLevel (f k)) := by
  classical
  have hex (k : ℕ) :
      ∃ j : ℕ, ∀ i,
        (R i).sourceLevel k ⊆ (P i).sourceLevel j :=
    synchronizedRefinement_sourceLevel
      P R hd LP LR hP hR hRP k
  let f : ℕ → ℕ := fun k => Classical.choose (hex k)
  have hsub (k : ℕ) (i : Fin d) :
      (R i).sourceLevel k ⊆ (P i).sourceLevel (f k) :=
    Classical.choose_spec (hex k) i
  let i0 : Fin d := ⟨0, hd⟩
  have hEq (k : ℕ) : LR k = LP (f k) := by
    obtain ⟨z, hz⟩ := (R i0).sourceLevel_nonempty k
    have hzP := hsub k i0 hz
    calc
      LR k = (R i0).levels k :=
        (congrFun (hR i0) k).symm
      _ = U.level z := hz.2.symm
      _ = (P i0).levels (f k) := hzP.2
      _ = LP (f k) := congrFun (hP i0) (f k)
  have hLP : StrictMono LP := by
    rw [← hP i0]
    exact (P i0).levels_strictMono
  have hLR : StrictMono LR := by
    rw [← hR i0]
    exact (R i0).levels_strictMono
  have hf : StrictMono f := by
    intro a b hab
    by_contra hbad
    have hba : f b ≤ f a := Nat.le_of_not_gt hbad
    have hp := hLP.monotone hba
    have hr := hLR hab
    rw [hEq a, hEq b] at hr
    omega
  exact ⟨f, hf, hEq, hsub⟩

/-- The family of genuine source-boundary cones associated
with one product-level tuple. -/
noncomputable def heterogeneousBoundaryCones
    (P : Fin d → StrongSubtree U)
    (n : ℕ) (base : HeterogeneousLevelTuple P n) :
    Fin d → StrongSubtree U :=
  fun i => boundaryCones (P i) n ⟨base.1 i, base.2 i⟩

theorem heterogeneousBoundaryCones_levels
    (P : Fin d → StrongSubtree U)
    (n : ℕ) (base : HeterogeneousLevelTuple P n)
    (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L) :
    ∀ i, (heterogeneousBoundaryCones P n base i).levels =
      fun k => L (n + k) := by
  intro i
  unfold heterogeneousBoundaryCones
  rw [boundaryCones_levels]
  funext k
  exact congrFun (hP i) (n + k)

/-- Synchronized refinements of the genuine boundary-cone
family all choose precisely one common subsequence of the
original boundary-cone source indices. -/
theorem exists_heterogeneousBoundary_commonIndex
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (n : ℕ) (base : HeterogeneousLevelTuple P n)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (R : Fin d → StrongSubtree U)
    (hR : ∀ i, (R i).levels = M)
    (hRB : ∀ i, (R i).Refines
      (heterogeneousBoundaryCones P n base i)) :
    ∃ f : ℕ → ℕ,
      StrictMono f ∧
      (∀ k, M k = L (n + f k)) ∧
      (∀ k i, (R i).sourceLevel k ⊆
        (heterogeneousBoundaryCones P n base i).sourceLevel (f k)) := by
  have hB :=
    heterogeneousBoundaryCones_levels P n base L hP
  exact exists_synchronizedRefinement_commonIndex
    (heterogeneousBoundaryCones P n base) R hd
    (fun k => L (n + k)) M hB hR hRB

end GeneralTree
end Milliken
