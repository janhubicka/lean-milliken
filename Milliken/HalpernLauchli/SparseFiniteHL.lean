import Milliken.HalpernLauchli.Lemma316BoundedTower
import Milliken.HalpernLauchli.FiniteHLCompactness
import Milliken.HalpernLauchli.FiniteHLTransport

/-!
# Finite Halpern--Läuchli on a sparse sequence of levels

Lemma 3.16 applies Theorem 3.9 not to every ambient tree level, but to the
subtree whose successive levels are the numbers `n₀<n₁<...` produced by
Lemma 3.15.  For the later contradiction it is important to remember this
extra information: in the color-one alternative the density base is on one
selected level and the dense target is the next selected level.

Rather than introducing a second tree datatype, we derive exactly this
finite statement from `HDHL` by the same compactness argument used for
`finiteHL_of_hdhl`.  In the asymmetric color-one alternative we move the
fixed base to a sufficiently high selected level before taking a finite
core.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Somewhere density measured between two consecutive selected levels. -/
def SparseSomewhereDense {d : ℕ}
    (levels : ℕ → ℕ) (M : Matrix ι d) : Prop :=
  ∃ q : ℕ, ∃ base : Fin d → Node ι,
    IsLevelVectorAt (levels q) base ∧
      M.DenseAbove base (levels (q + 1))

/-- Restricting a matrix which is dense above `base` to a higher base
preserves density, provided the new base is still below the target level. -/
theorem Matrix.restrictAbove_denseAbove_of_denseAbove
    {d n : ℕ}
    (M : Matrix ι d)
    (base next : Fin d → Node ι)
    (hM : M.DenseAbove base n)
    (hprefix : ∀ i, (base i).IsPrefix (next i))
    (hnext : ∀ i, (next i).length < n) :
    (M.restrictAbove next).DenseAbove next n := by
  intro i t ht
  have htbase : t ∈ coneLevel (base i) n :=
    ⟨(hprefix i).trans ht.1, ht.2⟩
  rcases hM i htbase with ⟨y, hyM, hty⟩
  refine ⟨y, ?_, hty⟩
  exact ⟨hyM, (ht.1).trans hty⟩

/-- A finite monochromatic witness whose color-one alternative is aligned
with the selected sparse levels. -/
structure SparseFiniteHLWitness
    (ι : Type u) (d k : ℕ) (levels : ℕ → ℕ) where
  M : Matrix ι d
  color : Fin 2
  coordFinite : ∀ i, (M.coord i).Finite
  shape :
    (color = 0 ∧ M.DenseAt k) ∨
      (color = 1 ∧ SparseSomewhereDense levels M)

namespace SparseFiniteHLWitness

variable {d k : ℕ} {levels : ℕ → ℕ}

theorem carrierFinite
    (W : SparseFiniteHLWitness ι d k levels) :
    W.M.carrier.Finite :=
  W.M.carrier_finite W.coordFinite

def cylinder
    (W : SparseFiniteHLWitness ι d k levels) :
    Set (BinaryColoring ι d) :=
  {c | ∀ x ∈ W.M.carrier, c x = W.color}

theorem cylinder_isOpen
    (W : SparseFiniteHLWitness ι d k levels) :
    IsOpen W.cylinder := by
  have heq :
      W.cylinder =
        ⋂ x ∈ W.M.carrier,
          {c : BinaryColoring ι d | c x = W.color} := by
    ext c
    simp [cylinder]
  rw [heq]
  apply W.carrierFinite.isOpen_biInter
  intro x hx
  change IsOpen ((fun c : BinaryColoring ι d => c x) ⁻¹' {W.color})
  exact (isOpen_discrete _).preimage (continuous_apply x)

/-- Maximum node length in one coordinate of a sparse witness. -/
noncomputable def coordBound
    (W : SparseFiniteHLWitness ι d k levels) (i : Fin d) : ℕ := by
  classical
  exact W.coordFinite i |>.toFinset.sup List.length

/-- Maximum node length occurring anywhere in a sparse witness. -/
noncomputable def nodeBound
    (W : SparseFiniteHLWitness ι d k levels) : ℕ := by
  classical
  exact Finset.univ.sup W.coordBound

theorem length_le_coordBound
    (W : SparseFiniteHLWitness ι d k levels)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ W.coordBound i := by
  classical
  unfold coordBound
  exact Finset.le_sup (f := List.length)
    (by simpa using hs)

theorem length_le_nodeBound
    (W : SparseFiniteHLWitness ι d k levels)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ W.nodeBound := by
  classical
  exact (W.length_le_coordBound hs).trans
    (Finset.le_sup (f := W.coordBound) (Finset.mem_univ i))

end SparseFiniteHLWitness

/-- Maximum support bound over a finite family of sparse witnesses. -/
noncomputable def sparseWitnessFamilyBound
    {d k : ℕ} {levels : ℕ → ℕ}
    (F : Finset (SparseFiniteHLWitness ι d k levels)) : ℕ := by
  classical
  exact F.sup SparseFiniteHLWitness.nodeBound

theorem sparseWitness_length_le_familyBound
    {d k : ℕ} {levels : ℕ → ℕ}
    {F : Finset (SparseFiniteHLWitness ι d k levels)}
    {W : SparseFiniteHLWitness ι d k levels}
    (hWF : W ∈ F)
    {i : Fin d} {s : Node ι}
    (hs : s ∈ W.M.coord i) :
    s.length ≤ sparseWitnessFamilyBound F := by
  classical
  exact (W.length_le_nodeBound hs).trans
    (Finset.le_sup (f := SparseFiniteHLWitness.nodeBound) hWF)

/-- Move a common-level vector to a prescribed higher level. -/
noncomputable def raiseLevelVector [Nonempty ι]
    {d : ℕ} (base : Fin d → Node ι) (l : ℕ) :
    Fin d → Node ι :=
  fun i => extendToLevel (base i) l

theorem raiseLevelVector_level [Nonempty ι]
    {d r l : ℕ}
    (base : Fin d → Node ι)
    (hbase : IsLevelVectorAt r base)
    (hrl : r ≤ l) :
    IsLevelVectorAt l (raiseLevelVector base l) := by
  intro i
  dsimp [raiseLevelVector]
  exact length_extendToLevel (by simpa [hbase i] using hrl)

theorem prefix_raiseLevelVector [Nonempty ι]
    {d r l : ℕ}
    (base : Fin d → Node ι)
    (hbase : IsLevelVectorAt r base)
    (hrl : r ≤ l) :
    ∀ i, (base i).IsPrefix (raiseLevelVector base l i) := by
  intro i
  dsimp [raiseLevelVector]
  exact prefix_extendToLevel _ _

/-- Every binary coloring has a finite sparse-level witness. -/
theorem exists_sparseFiniteHLWitness_of_hdhl
    [Finite ι] [Nonempty ι]
    {d k : ℕ} {levels : ℕ → ℕ}
    (hHDHL : HDHL ι d)
    (hk : 0 < k)
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q)
    (c : BinaryColoring ι d) :
    ∃ W : SparseFiniteHLWitness ι d k levels,
      c ∈ W.cylinder := by
  classical
  let K0 : Set (Fin d → Node ι) := {x | c x = 0}
  rcases asymmetric_of_hdhl hHDHL K0 with hzero | hone
  · rcases hzero k hk with ⟨M, hMdense, hMsub⟩
    let N : Matrix ι d := M.finiteDenseCore hMdense
    let W : SparseFiniteHLWitness ι d k levels := {
      M := N
      color := 0
      coordFinite := by
        dsimp [N]
        exact M.finiteDenseCore_coord_finite hMdense
      shape := Or.inl ⟨rfl, by
        dsimp [N]
        exact M.finiteDenseCore_dense hMdense⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxM : x ∈ M.carrier :=
      M.finiteDenseCore_subset hMdense hx
    exact hMsub hxM
  · rcases hone with ⟨base, ⟨r, hbase⟩, hall⟩
    rcases hunbounded r with ⟨q, hrq⟩
    let raised : Fin d → Node ι :=
      raiseLevelVector base (levels q)
    have hraised :
        IsLevelVectorAt (levels q) raised := by
      dsimp [raised]
      exact raiseLevelVector_level base hbase hrq
    have hpref : ∀ i, (base i).IsPrefix (raised i) := by
      dsimp [raised]
      exact prefix_raiseLevelVector base hbase hrq
    have hnext :
        ∀ i, (raised i).length < levels (q + 1) := by
      intro i
      rw [hraised i]
      exact hlevels (Nat.lt_succ_self q)
    rcases hall (levels (q + 1)) with
      ⟨M, hMdense, hMsub⟩
    let R : Matrix ι d := M.restrictAbove raised
    have hRdense :
        R.DenseAbove raised (levels (q + 1)) := by
      dsimp [R]
      exact M.restrictAbove_denseAbove_of_denseAbove
        base raised hMdense hpref hnext
    let N : Matrix ι d :=
      R.finiteDenseAboveCore raised hRdense
    have hNsparse :
        SparseSomewhereDense levels N := by
      refine ⟨q, raised, hraised, ?_⟩
      dsimp [N]
      exact R.finiteDenseAboveCore_dense raised hRdense
    let W : SparseFiniteHLWitness ι d k levels := {
      M := N
      color := 1
      coordFinite := by
        dsimp [N]
        exact R.finiteDenseAboveCore_coord_finite raised hRdense
      shape := Or.inr ⟨rfl, hNsparse⟩
    }
    refine ⟨W, ?_⟩
    intro x hx
    have hxR : x ∈ R.carrier :=
      R.finiteDenseAboveCore_subset raised hRdense hx
    have hxM : x ∈ M.carrier := by
      dsimp [R] at hxR
      exact M.restrictAbove_carrier_subset raised hxR
    have hx1 : x ∈ K0ᶜ := hMsub hxM
    have hne : c x ≠ (0 : Fin 2) := by
      intro h0
      exact hx1 h0
    exact Fin.eq_one_of_ne_zero (c x) hne

/-- The sparse witness cylinders cover all binary colorings. -/
theorem sparseFiniteHLWitness_cover
    [Finite ι] [Nonempty ι]
    {d k : ℕ} {levels : ℕ → ℕ}
    (hHDHL : HDHL ι d)
    (hk : 0 < k)
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    (Set.univ : Set (BinaryColoring ι d)) ⊆
      ⋃ W : SparseFiniteHLWitness ι d k levels, W.cylinder := by
  intro c hc
  rcases exists_sparseFiniteHLWitness_of_hdhl
      hHDHL hk hlevels hunbounded c with ⟨W, hW⟩
  exact Set.mem_iUnion.2 ⟨W, hW⟩

/-- Compactness reduces the sparse finite theorem to finitely many finite
witnesses. -/
theorem exists_sparseFiniteHLWitness_subcover
    [Finite ι] [Nonempty ι]
    {d k : ℕ} {levels : ℕ → ℕ}
    (hHDHL : HDHL ι d)
    (hk : 0 < k)
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    ∃ F : Finset (SparseFiniteHLWitness ι d k levels),
      (Set.univ : Set (BinaryColoring ι d)) ⊆
        ⋃ W ∈ F, W.cylinder := by
  classical
  exact isCompact_univ.elim_finite_subcover
    (fun W : SparseFiniteHLWitness ι d k levels => W.cylinder)
    (fun W => W.cylinder_isOpen)
    (sparseFiniteHLWitness_cover hHDHL hk hlevels hunbounded)

/-- Coordinatewise image of a sparse witness inside an ambient dense
matrix. -/
noncomputable def transportSparseWitness
    [Nonempty ι]
    {d k l : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l) :
    Matrix ι d where
  coord := fun i =>
    extendIntoDense M hM i '' W.M.coord i

theorem transportSparseWitness_subset
    [Nonempty ι]
    {d k l : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l) :
    (transportSparseWitness W M hM).carrier ⊆ M.carrier := by
  intro z hz i
  rcases hz i with ⟨s, hs, hsz⟩
  rw [← hsz]
  exact extendIntoDense_mem M hM i s

theorem exists_source_of_mem_transportSparseWitness
    [Nonempty ι]
    {d k l : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l)
    {z : Fin d → Node ι}
    (hz : z ∈ (transportSparseWitness W M hM).carrier) :
    ∃ x ∈ W.M.carrier,
      ∀ i, extendIntoDense M hM i (x i) = z i := by
  classical
  choose x hxW hx using fun i => hz i
  refine ⟨x, ?_, hx⟩
  intro i
  exact hxW i

theorem transportSparseWitness_dense
    [Nonempty ι]
    {d k l : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l)
    (hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l)
    (hW : W.M.DenseAt k) :
    (transportSparseWitness W M hM).DenseAt k := by
  intro i s hs
  rcases hW i hs with ⟨y, hyW, hsy⟩
  refine ⟨extendIntoDense M hM i y, ?_,
    hsy.trans (prefix_extendIntoDense M hM i y
      (hbound i y hyW))⟩
  exact ⟨y, hyW, rfl⟩

theorem transportSparseWitness_denseAbove
    [Nonempty ι]
    {d k l q : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l)
    (hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l)
    (base : Fin d → Node ι)
    (hW : W.M.DenseAbove base q) :
    (transportSparseWitness W M hM).DenseAbove base q := by
  intro i s hs
  rcases hW i hs with ⟨y, hyW, hsy⟩
  refine ⟨extendIntoDense M hM i y, ?_,
    hsy.trans (prefix_extendIntoDense M hM i y
      (hbound i y hyW))⟩
  exact ⟨y, hyW, rfl⟩

theorem transportSparseWitness_sparse
    [Nonempty ι]
    {d k l : ℕ} {levels : ℕ → ℕ}
    (W : SparseFiniteHLWitness ι d k levels)
    (M : Matrix ι d) (hM : M.DenseAt l)
    (hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l)
    (hW : SparseSomewhereDense levels W.M) :
    SparseSomewhereDense levels (transportSparseWitness W M hM) := by
  rcases hW with ⟨q, base, hbase, hdense⟩
  refine ⟨q, base, hbase, ?_⟩
  exact transportSparseWitness_denseAbove W M hM hbound base hdense

/-- Finite Halpern--Läuchli aligned with a prescribed strictly increasing,
unbounded sequence of levels. -/
theorem sparseFiniteHL_of_hdhl
    [Finite ι] [Nonempty ι]
    {d k : ℕ} {levels : ℕ → ℕ}
    (hHDHL : HDHL ι d)
    (hk : 0 < k)
    (hlevels : StrictMono levels)
    (hunbounded : ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q) :
    ∃ l : ℕ, ∀ M : Matrix ι d,
      M.DenseAt l →
      ∀ K0 : Set (Fin d → Node ι),
        (∃ M1 : Matrix ι d,
            SparseSomewhereDense levels M1 ∧
            M1.carrier ⊆ M.carrier ∩ K0ᶜ) ∨
        (∃ M0 : Matrix ι d,
            M0.DenseAt k ∧
            M0.carrier ⊆ M.carrier ∩ K0) := by
  classical
  rcases exists_sparseFiniteHLWitness_subcover
      hHDHL hk hlevels hunbounded with
    ⟨F, hcover⟩
  let L : ℕ := sparseWitnessFamilyBound F
  let l : ℕ := max k L
  refine ⟨l, ?_⟩
  intro M hM K0
  let mapTuple : (Fin d → Node ι) → (Fin d → Node ι) :=
    fun x i => extendIntoDense M hM i (x i)
  let c : BinaryColoring ι d :=
    fun x => if mapTuple x ∈ K0 then 0 else 1
  have hc :
      c ∈ ⋃ W ∈ F, W.cylinder :=
    hcover (Set.mem_univ c)
  simp only [Set.mem_iUnion] at hc
  rcases hc with ⟨W, hWF, hcW⟩
  have hbound :
      ∀ i s, s ∈ W.M.coord i → s.length ≤ l := by
    intro i s hs
    have hL : s.length ≤ L := by
      dsimp [L]
      exact sparseWitness_length_le_familyBound hWF hs
    dsimp [l]
    exact hL.trans (Nat.le_max_right _ _)
  let N : Matrix ι d := transportSparseWitness W M hM
  have hNsubM : N.carrier ⊆ M.carrier := by
    dsimp [N]
    exact transportSparseWitness_subset W M hM
  rcases W.shape with hzero | hone
  · right
    rcases hzero with ⟨hcolor, hWdense⟩
    have hNdense : N.DenseAt k := by
      dsimp [N]
      exact transportSparseWitness_dense W M hM hbound hWdense
    refine ⟨N, hNdense, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    rcases exists_source_of_mem_transportSparseWitness
        W M hM hz with ⟨x, hxW, hxmap⟩
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 0 :=
      (hcW x hxW).trans hcolor
    by_contra hzK
    have hcx1 : c x = 1 := by
      simp [c, hmap, hzK]
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcx.symm.trans hcx1)
  · left
    rcases hone with ⟨hcolor, hWsparse⟩
    have hNsparse : SparseSomewhereDense levels N := by
      dsimp [N]
      exact transportSparseWitness_sparse
        W M hM hbound hWsparse
    refine ⟨N, hNsparse, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    intro hzK
    rcases exists_source_of_mem_transportSparseWitness
        W M hM hz with ⟨x, hxW, hxmap⟩
    have hmap : mapTuple x = z := by
      funext i
      exact hxmap i
    have hcx : c x = 1 :=
      (hcW x hxW).trans hcolor
    have hcx0 : c x = 0 := by
      simp [c, hmap, hzK]
    exact (by decide : (1 : Fin 2) ≠ 0)
      (hcx.symm.trans hcx0)

end HalpernLauchli
end Milliken
