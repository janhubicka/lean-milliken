import Milliken.GeneralTree.HeterogeneousSomewhereDense

/-!
# Finite dense-matrix cores for arbitrary heterogeneous strong trees

A dense matrix can be made finite by choosing one extension of each
node at the requested selected source level.  The same is true for
density above an arbitrary coordinatewise base tuple.

Both constructions use finiteness of *individual* selected source
levels; no uniform bound on the branching degrees is assumed.
They are the finite-witness compactness inputs for the heterogeneous
form of the sparse finite Halpern--Läuchli theorem in Todorčević §3.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ} {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- A cartesian matrix with finitely many points in each coordinate
has a finite carrier, including in dimension zero. -/
theorem carrier_finite
    (M : HeterogeneousMatrix P)
    (hfin : ∀ i, (M.coord i).Finite) :
    M.carrier.Finite := by
  simpa [carrier] using Set.Finite.pi' hfin

/-- Choose an M-point above each node of an actual selected source
level. The domain is finite even when the ambient degrees are
unbounded as a function of the level. -/
noncomputable def denseChoice
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : SourceBoundary (P i) k) : U :=
  Classical.choose (hM i s.1 s.2)

theorem denseChoice_mem
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : SourceBoundary (P i) k) :
    M.denseChoice hM i s ∈ M.coord i :=
  (Classical.choose_spec (hM i s.1 s.2)).1

theorem denseChoice_le
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : SourceBoundary (P i) k) :
    s.1 ≤ M.denseChoice hM i s :=
  (Classical.choose_spec (hM i s.1 s.2)).2

/-- The finite matrix obtained by retaining one chosen extension
for each node on the specified source level. -/
noncomputable def finiteDenseCore
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k) : HeterogeneousMatrix P where
  coord := fun i => Set.range (M.denseChoice hM i)
  coord_sub := by
    intro i z hz
    obtain ⟨s, rfl⟩ := hz
    exact M.coord_sub i (M.denseChoice_mem hM i s)

theorem finiteDenseCore_coord_finite
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k) :
    ∀ i, ((M.finiteDenseCore hM).coord i).Finite := by
  intro i
  letI : Finite (SourceBoundary (P i) k) :=
    sourceBoundary_finite (P i) k
  exact Set.finite_range _

theorem finiteDenseCore_carrier_finite
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k) :
    (M.finiteDenseCore hM).carrier.Finite :=
  (M.finiteDenseCore hM).carrier_finite
    (M.finiteDenseCore_coord_finite hM)

theorem finiteDenseCore_denseAt
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k) :
    (M.finiteDenseCore hM).DenseAt k := by
  intro i s hs
  let q : SourceBoundary (P i) k := ⟨s, hs⟩
  exact ⟨M.denseChoice hM i q, ⟨q, rfl⟩,
    M.denseChoice_le hM i q⟩

theorem finiteDenseCore_subset
    (M : HeterogeneousMatrix P) {k : ℕ}
    (hM : M.DenseAt k) :
    (M.finiteDenseCore hM).carrier ⊆ M.carrier := by
  intro x hx i
  obtain ⟨s, hs⟩ := hx i
  rw [← hs]
  exact M.denseChoice_mem hM i s

/-- Finite source-level test nodes belonging to the cone above
the i-th base coordinate. -/
abbrev ConeSourceBoundary
    (P : Fin d → StrongSubtree U)
    (base : Fin d → U)
    (i : Fin d) (k : ℕ) :=
  {x : U // x ∈ (P i).sourceLevel k ∧ base i ≤ x}

instance coneSourceBoundary_finite
    (P : Fin d → StrongSubtree U)
    (base : Fin d → U)
    (i : Fin d) (k : ℕ) :
    Finite (ConeSourceBoundary P base i k) := by
  have hfin : ({x : U |
      x ∈ (P i).sourceLevel k ∧ base i ≤ x} : Set U).Finite :=
    ((P i).sourceLevel_finite k).subset (fun _ hx => hx.1)
  exact hfin.to_subtype

/-- Choose a retained point of M above any source-level-k node
in the actual cone of the specified base coordinate. -/
noncomputable def denseAboveChoice
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : ConeSourceBoundary P base i k) : U :=
  Classical.choose (hM i s.1 s.2.1 s.2.2)

theorem denseAboveChoice_mem
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : ConeSourceBoundary P base i k) :
    M.denseAboveChoice base hM i s ∈ M.coord i :=
  (Classical.choose_spec (hM i s.1 s.2.1 s.2.2)).1

theorem denseAboveChoice_le
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : ConeSourceBoundary P base i k) :
    s.1 ≤ M.denseAboveChoice base hM i s :=
  (Classical.choose_spec (hM i s.1 s.2.1 s.2.2)).2

/-- A finite submatrix preserving the original cone-density scale. -/
noncomputable def finiteDenseAboveCore
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k) : HeterogeneousMatrix P where
  coord := fun i => Set.range (M.denseAboveChoice base hM i)
  coord_sub := by
    intro i z hz
    obtain ⟨s, rfl⟩ := hz
    exact M.coord_sub i (M.denseAboveChoice_mem base hM i s)

theorem finiteDenseAboveCore_coord_finite
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k) :
    ∀ i, ((M.finiteDenseAboveCore base hM).coord i).Finite := by
  intro i
  letI : Finite (ConeSourceBoundary P base i k) :=
    coneSourceBoundary_finite P base i k
  exact Set.finite_range _

theorem finiteDenseAboveCore_carrier_finite
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (M.finiteDenseAboveCore base hM).carrier.Finite :=
  (M.finiteDenseAboveCore base hM).carrier_finite
    (M.finiteDenseAboveCore_coord_finite base hM)

theorem finiteDenseAboveCore_denseAbove
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (M.finiteDenseAboveCore base hM).DenseAbove base k := by
  intro i s hs hbase
  let q : ConeSourceBoundary P base i k :=
    ⟨s, hs, hbase⟩
  exact ⟨M.denseAboveChoice base hM i q, ⟨q, rfl⟩,
    M.denseAboveChoice_le base hM i q⟩

theorem finiteDenseAboveCore_subset
    (M : HeterogeneousMatrix P)
    (base : Fin d → U) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (M.finiteDenseAboveCore base hM).carrier ⊆ M.carrier := by
  intro x hx i
  obtain ⟨s, hs⟩ := hx i
  rw [← hs]
  exact M.denseAboveChoice_mem base hM i s

end HeterogeneousMatrix
end GeneralTree
end Milliken
