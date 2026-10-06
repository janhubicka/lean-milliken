import Milliken.HalpernLauchli.SelectedLevelShift

/-!
# Matrices under selected-level cone shifts

A selected-level cone above a common-level base vector is identified with
the product of shifted trees by coordinatewise prefixing/dropping the base.
This file lifts the node-level equivalence to matrices and proves that global
density in the shifted tree is exactly cone density in the original tree at
the corresponding selected level.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- Prefix a tail tuple by a fixed base vector. -/
def prependTuple {d : ℕ}
    (base : Fin d → Node ι)
    (x : Fin d → Node ι) :
    Fin d → Node ι :=
  fun i => base i ++ x i

/-- Drop a fixed base prefix coordinatewise. -/
def dropTuple {d : ℕ}
    (base : Fin d → Node ι)
    (x : Fin d → Node ι) :
    Fin d → Node ι :=
  fun i => (x i).drop (base i).length

/-- Pull a product set back to the tails above a fixed base vector. -/
def conePullback {d : ℕ}
    (base : Fin d → Node ι)
    (P : Set (Fin d → Node ι)) :
    Set (Fin d → Node ι) :=
  {x | prependTuple base x ∈ P}

namespace Matrix

/-- Prefix each coordinate of a tail matrix by the corresponding base. -/
def prepend {d : ℕ}
    (base : Fin d → Node ι)
    (M : Matrix ι d) :
    Matrix ι d where
  coord := fun i =>
    (fun t => base i ++ t) '' M.coord i

/-- Keep the part of a matrix above the base and drop that base prefix. -/
def dropAbove {d : ℕ}
    (base : Fin d → Node ι)
    (M : Matrix ι d) :
    Matrix ι d where
  coord := fun i =>
    (fun y => y.drop (base i).length) ''
      {y | y ∈ M.coord i ∧ (base i).IsPrefix y}

theorem prepend_mem_carrier_iff
    {d : ℕ}
    (base : Fin d → Node ι)
    (M : Matrix ι d)
    (x : Fin d → Node ι) :
    prependTuple base x ∈ (M.prepend base).carrier ↔
      x ∈ M.carrier := by
  constructor
  · intro hx i
    rcases hx i with ⟨y, hyM, hy⟩
    have happ : base i ++ x i = base i ++ y := by
      simpa [prependTuple] using hy.symm
    exact hyM (List.append_left_injective happ)
  · intro hx i
    exact ⟨x i, hx i, by simp [prependTuple]⟩

theorem prepend_carrier_subset_of_pullback
    {d : ℕ}
    (base : Fin d → Node ι)
    (M : Matrix ι d)
    (P : Set (Fin d → Node ι))
    (hM : M.carrier ⊆ conePullback base P) :
    (M.prepend base).carrier ⊆ P := by
  intro z hz
  choose x hxM hxz using fun i => hz i
  have hxCarrier : x ∈ M.carrier := by
    intro i
    exact hxM i
  have hxP : prependTuple base x ∈ P :=
    hM hxCarrier
  have hzEq : prependTuple base x = z := by
    funext i
    exact hxz i
  rwa [hzEq] at hxP

/-- Density in a shifted selected-level tree becomes cone density after
prefixing the common-level base. -/
theorem prepend_denseAbove
    {d m n : ℕ}
    (S : Selection)
    (base : Fin d → Node ι)
    (hbase : IsLevelVectorAt (S.levels m) base)
    (M : Matrix ι d)
    (hM : M.DenseAt ((shift S m).levels n)) :
    (M.prepend base).DenseAbove base (S.levels (m + n)) := by
  intro i z hz
  let t : Node ι := (z.drop (base i).length)
  have htlen :
      t.length = (shift S m).levels n := by
    dsimp [t]
    rw [List.length_drop, hz.2, hbase i, shift_levels]
  rcases hM i
      (show t ∈ treeLevel (ι := ι) ((shift S m).levels n)
        from htlen) with
    ⟨y, hyM, hty⟩
  refine ⟨base i ++ y, ?_, ?_⟩
  · exact ⟨y, hyM, rfl⟩
  · have hreconstruct :
        base i ++ t = z := by
      dsimp [t]
      have htake :
          z.take (base i).length = base i :=
        (List.prefix_iff_eq_take.mp hz.1).symm
      simpa [htake] using
        (List.take_append_drop (base i).length z)
    rw [← hreconstruct]
    exact StrongEmbedding.prefix_append_left (base i) hty

/-- Cone density becomes global density after dropping the common base
prefix. -/
theorem dropAbove_denseAt
    {d m n : ℕ}
    (S : Selection)
    (base : Fin d → Node ι)
    (hbase : IsLevelVectorAt (S.levels m) base)
    (M : Matrix ι d)
    (hM : M.DenseAbove base (S.levels (m + n))) :
    (M.dropAbove base).DenseAt ((shift S m).levels n) := by
  intro i t ht
  let z : Node ι := base i ++ t
  have hzlen : z.length = S.levels (m + n) := by
    dsimp [z]
    rw [List.length_append, hbase i, ht]
    exact level_add_shift S m n
  have hzcone :
      z ∈ coneLevel (base i) (S.levels (m + n)) :=
    ⟨List.prefix_append _ _, hzlen⟩
  rcases hM i hzcone with ⟨y, hyM, hzy⟩
  refine ⟨y.drop (base i).length, ?_, ?_⟩
  · refine ⟨y, ⟨hyM, ?_⟩, rfl⟩
    exact hzcone.1.trans hzy
  · have hdrop := hzy.drop (base i).length
    change t.IsPrefix (y.drop (base i).length)
    simpa [z] using hdrop

/-- Dropping a matrix already contained in a cone-pullback keeps it inside
the pulled-back set. -/
theorem dropAbove_carrier_subset
    {d : ℕ}
    (base : Fin d → Node ι)
    (M : Matrix ι d)
    (P : Set (Fin d → Node ι))
    (hM : M.carrier ⊆ P)
    (hcone :
      ∀ x ∈ M.carrier, ∀ i,
        (base i).IsPrefix (x i)) :
    (M.dropAbove base).carrier ⊆ conePullback base P := by
  intro t ht
  choose y hyM hyt using fun i => ht i
  have hyCarrier : y ∈ M.carrier := by
    intro i
    exact (hyM i).1
  have hyP : y ∈ P := hM hyCarrier
  change prependTuple base t ∈ P
  have hEq : prependTuple base t = y := by
    funext i
    have hpre : (base i).IsPrefix (y i) :=
      hcone y hyCarrier i
    have hreconstruct :
        base i ++ (y i).drop (base i).length = y i := by
      have htake :
          (y i).take (base i).length = base i :=
        (List.prefix_iff_eq_take.mp hpre).symm
      simpa [htake] using
        (List.take_append_drop (base i).length (y i))
    rw [← hyt i]
    exact hreconstruct
  rwa [hEq]

end Matrix

end SelectedLevelTree
end HalpernLauchli
end Milliken
