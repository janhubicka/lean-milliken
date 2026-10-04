import Milliken.HalpernLauchli.FiniteHLCompactness

/-!
# Transporting finite Halpern--Läuchli witnesses into a dense matrix

A finite subcover gives finitely many finite monochromatic witness matrices.
Choose one level above every node appearing in those witnesses.  If an
ambient matrix is dense at that level, each witness node can be extended
coordinatewise into the ambient matrix.  The extension preserves all prefix
relations relevant to density, hence preserves both `DenseAt` and
`SomewhereDense`.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace FiniteHLWitness

variable {d k : ℕ}

/-- Maximum node length occurring in one coordinate of a finite witness. -/
noncomputable def coordBound
    (W : FiniteHLWitness ι d k) (i : Fin d) : ℕ := by
  classical
  exact W.coordFinite i |>.toFinset.sup List.length

/-- Maximum node length occurring anywhere in a finite witness. -/
noncomputable def nodeBound
    (W : FiniteHLWitness ι d k) : ℕ := by
  classical
  exact Finset.univ.sup W.coordBound

theorem length_le_coordBound
    (W : FiniteHLWitness ι d k)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ W.coordBound i := by
  classical
  unfold coordBound
  exact Finset.le_sup (f := List.length)
    (by simpa using hs)

theorem length_le_nodeBound
    (W : FiniteHLWitness ι d k)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ W.nodeBound := by
  classical
  exact (W.length_le_coordBound hs).trans
    (Finset.le_sup (f := W.coordBound) (Finset.mem_univ i))

end FiniteHLWitness

/-- Maximum support bound over a finite family of witnesses. -/
noncomputable def finiteWitnessFamilyBound
    {d k : ℕ}
    (F : Finset (FiniteHLWitness ι d k)) : ℕ := by
  classical
  exact F.sup FiniteHLWitness.nodeBound

theorem witness_length_le_familyBound
    {d k : ℕ}
    {F : Finset (FiniteHLWitness ι d k)}
    {W : FiniteHLWitness ι d k}
    (hWF : W ∈ F)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ finiteWitnessFamilyBound F := by
  classical
  exact (W.length_le_nodeBound hs).trans
    (Finset.le_sup (f := FiniteHLWitness.nodeBound) hWF)

/-- A source node padded to the target ambient level when possible; an
arbitrary canonical node on that level otherwise. -/
noncomputable def targetAtLevel [Nonempty ι]
    (l : ℕ) (s : Node ι) : Node ι :=
  if hs : s.length ≤ l then extendToLevel s l
  else rayNode (ι := ι) l

theorem targetAtLevel_length [Nonempty ι]
    (l : ℕ) (s : Node ι) :
    (targetAtLevel l s).length = l := by
  classical
  unfold targetAtLevel
  split
  · exact length_extendToLevel ‹s.length ≤ l›
  · exact rayNode_length l

theorem prefix_targetAtLevel [Nonempty ι]
    {l : ℕ} {s : Node ι}
    (hs : s.length ≤ l) :
    s.IsPrefix (targetAtLevel l s) := by
  classical
  rw [targetAtLevel, dif_pos hs]
  exact prefix_extendToLevel _ _

/-- Extend a node into coordinate `i` of an ambient `l`-dense matrix. -/
noncomputable def extendIntoDense [Nonempty ι]
    {d l : ℕ}
    (M : Matrix ι d) (hM : M.DenseAt l)
    (i : Fin d) (s : Node ι) : Node ι :=
  Classical.choose
    (hM i
      (show targetAtLevel l s ∈ treeLevel (ι := ι) l from
        targetAtLevel_length l s))

theorem extendIntoDense_mem [Nonempty ι]
    {d l : ℕ}
    (M : Matrix ι d) (hM : M.DenseAt l)
    (i : Fin d) (s : Node ι) :
    extendIntoDense M hM i s ∈ M.coord i :=
  (Classical.choose_spec
    (hM i
      (show targetAtLevel l s ∈ treeLevel (ι := ι) l from
        targetAtLevel_length l s))).1

theorem prefix_extendIntoDense [Nonempty ι]
    {d l : ℕ}
    (M : Matrix ι d) (hM : M.DenseAt l)
    (i : Fin d) (s : Node ι)
    (hs : s.length ≤ l) :
    s.IsPrefix (extendIntoDense M hM i s) :=
  (prefix_targetAtLevel hs).trans
    (Classical.choose_spec
      (hM i
        (show targetAtLevel l s ∈ treeLevel (ι := ι) l from
          targetAtLevel_length l s))).2

/-- Coordinatewise image of a finite witness inside an ambient dense
matrix. -/
noncomputable def transportWitness
    [Nonempty ι]
    {d k l : ℕ}
    (W : FiniteHLWitness ι d k)
    (M : Matrix ι d) (hM : M.DenseAt l) :
    Matrix ι d where
  coord := fun i =>
    extendIntoDense M hM i '' W.M.coord i

theorem transportWitness_subset
    [Nonempty ι]
    {d k l : ℕ}
    (W : FiniteHLWitness ι d k)
    (M : Matrix ι d) (hM : M.DenseAt l) :
    (transportWitness W M hM).carrier ⊆ M.carrier := by
  intro z hz i
  rcases hz i with ⟨s, hs, hsz⟩
  rw [← hsz]
  exact extendIntoDense_mem M hM i s

theorem exists_source_of_mem_transportWitness
    [Nonempty ι]
    {d k l : ℕ}
    (W : FiniteHLWitness ι d k)
    (M : Matrix ι d) (hM : M.DenseAt l)
    {z : Fin d → Node ι}
    (hz : z ∈ (transportWitness W M hM).carrier) :
    ∃ x ∈ W.M.carrier,
      ∀ i, extendIntoDense M hM i (x i) = z i := by
  classical
  choose x hxW hx using fun i => hz i
  refine ⟨x, ?_, hx⟩
  intro i
  exact hxW i

theorem transportWitness_dense
    [Nonempty ι]
    {d k l : ℕ}
    (W : FiniteHLWitness ι d k)
    (M : Matrix ι d) (hM : M.DenseAt l)
    (hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l)
    (hW : W.M.DenseAt k) :
    (transportWitness W M hM).DenseAt k := by
  intro i s hs
  rcases hW i hs with ⟨y, hyW, hsy⟩
  refine ⟨extendIntoDense M hM i y, ?_,
    hsy.trans (prefix_extendIntoDense M hM i y
      (hbound i y hyW))⟩
  exact ⟨y, hyW, rfl⟩

theorem transportWitness_somewhereDense
    [Nonempty ι]
    {d k l : ℕ}
    (W : FiniteHLWitness ι d k)
    (M : Matrix ι d) (hM : M.DenseAt l)
    (hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l)
    (hW : W.M.SomewhereDense) :
    (transportWitness W M hM).SomewhereDense := by
  rcases hW with ⟨base, q, hbase, hdense⟩
  refine ⟨base, q, hbase, ?_⟩
  intro i s hs
  rcases hdense i hs with ⟨y, hyW, hsy⟩
  refine ⟨extendIntoDense M hM i y, ?_,
    hsy.trans (prefix_extendIntoDense M hM i y
      (hbound i y hyW))⟩
  exact ⟨y, hyW, rfl⟩

end HalpernLauchli
end Milliken
