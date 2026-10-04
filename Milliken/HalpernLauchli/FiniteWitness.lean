import Milliken.HalpernLauchli.FiniteHL
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Instances.Fin

/-!
# Finite witnesses for the compactness proof of Theorem 3.9

Every dense-matrix witness can be thinned to a finite one.
For each target node on the finite target level, choose one node of the
corresponding matrix coordinate extending it.  The ranges of these choice
maps are finite and retain the required density.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

theorem finite_treeLevel [Finite ι] (k : ℕ) :
    (treeLevel (ι := ι) k).Finite :=
  List.finite_length_eq ι k

theorem finite_coneLevel [Finite ι]
    (s : Node ι) (k : ℕ) :
    (coneLevel s k).Finite :=
  (finite_treeLevel (ι := ι) k).subset fun _ h => h.2

namespace Matrix

variable {d : ℕ}

theorem carrier_finite
    (M : Matrix ι d)
    (hfin : ∀ i, (M.coord i).Finite) :
    M.carrier.Finite := by
  simpa [carrier] using Set.Finite.pi' hfin

noncomputable def denseChoice
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : treeLevel (ι := ι) k) :
    Node ι :=
  Classical.choose (hM i s.1 s.2)

theorem denseChoice_mem
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : treeLevel (ι := ι) k) :
    denseChoice M hM i s ∈ M.coord i :=
  (Classical.choose_spec (hM i s.1 s.2)).1

theorem denseChoice_prefix
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k)
    (i : Fin d) (s : treeLevel (ι := ι) k) :
    s.1.IsPrefix (denseChoice M hM i s) :=
  (Classical.choose_spec (hM i s.1 s.2)).2

noncomputable def finiteDenseCore [Finite ι]
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    Matrix ι d where
  coord := fun i => Set.range (denseChoice M hM i)

theorem finiteDenseCore_coord_finite [Finite ι]
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    ∀ i, ((finiteDenseCore M hM).coord i).Finite := by
  intro i
  letI : Finite (treeLevel (ι := ι) k) :=
    (finite_treeLevel (ι := ι) k).to_subtype
  exact Set.finite_range _

theorem finiteDenseCore_carrier_finite [Finite ι]
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    (finiteDenseCore M hM).carrier.Finite :=
  (finiteDenseCore M hM).carrier_finite
    (finiteDenseCore_coord_finite M hM)

theorem finiteDenseCore_dense [Finite ι]
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    (finiteDenseCore M hM).DenseAt k := by
  intro i s hs
  let q : treeLevel (ι := ι) k := ⟨s, hs⟩
  refine ⟨denseChoice M hM i q, ?_, denseChoice_prefix M hM i q⟩
  exact ⟨q, rfl⟩

theorem finiteDenseCore_subset [Finite ι]
    (M : Matrix ι d) {k : ℕ}
    (hM : M.DenseAt k) :
    (finiteDenseCore M hM).carrier ⊆ M.carrier := by
  intro z hz i
  rcases hz i with ⟨s, rfl⟩
  exact denseChoice_mem M hM i s

noncomputable def denseAboveChoice
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : coneLevel (base i) k) :
    Node ι :=
  Classical.choose (hM i s.1 s.2)

theorem denseAboveChoice_mem
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : coneLevel (base i) k) :
    denseAboveChoice M base hM i s ∈ M.coord i :=
  (Classical.choose_spec (hM i s.1 s.2)).1

theorem denseAboveChoice_prefix
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k)
    (i : Fin d) (s : coneLevel (base i) k) :
    s.1.IsPrefix (denseAboveChoice M base hM i s) :=
  (Classical.choose_spec (hM i s.1 s.2)).2

noncomputable def finiteDenseAboveCore [Finite ι]
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k) :
    Matrix ι d where
  coord := fun i => Set.range (denseAboveChoice M base hM i)

theorem finiteDenseAboveCore_coord_finite [Finite ι]
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k) :
    ∀ i, ((finiteDenseAboveCore M base hM).coord i).Finite := by
  intro i
  letI : Finite (coneLevel (base i) k) :=
    (finite_coneLevel (ι := ι) (base i) k).to_subtype
  exact Set.finite_range _

theorem finiteDenseAboveCore_carrier_finite [Finite ι]
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (finiteDenseAboveCore M base hM).carrier.Finite :=
  (finiteDenseAboveCore M base hM).carrier_finite
    (finiteDenseAboveCore_coord_finite M base hM)

theorem finiteDenseAboveCore_dense [Finite ι]
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (finiteDenseAboveCore M base hM).DenseAbove base k := by
  intro i s hs
  let q : coneLevel (base i) k := ⟨s, hs⟩
  refine ⟨denseAboveChoice M base hM i q, ?_,
    denseAboveChoice_prefix M base hM i q⟩
  exact ⟨q, rfl⟩

theorem finiteDenseAboveCore_subset [Finite ι]
    (M : Matrix ι d)
    (base : Fin d → Node ι) {k : ℕ}
    (hM : M.DenseAbove base k) :
    (finiteDenseAboveCore M base hM).carrier ⊆ M.carrier := by
  intro z hz i
  rcases hz i with ⟨s, rfl⟩
  exact denseAboveChoice_mem M base hM i s

end Matrix
end HalpernLauchli
end Milliken
