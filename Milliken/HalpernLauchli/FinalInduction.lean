import Milliken.HalpernLauchli.Lemma316

/-!
# The stabilized final induction step for HDHL

After Lemma 3.16, Todorčević finishes the induction by running through the
finitely many immediate successors of the last tree root.  At each stage a
new section matrix is chosen at a later level.  We explicitly refine the new
matrix above the previous one; this is the harmless thinning which makes the
printed appeal to stabilization completely formal.

This file proves the final step under the two standing reductions used in
Section 3.2:

* the complement of `P` contains no somewhere-dense matrix;
* `P` already satisfies the stabilization property (*).

The preceding fusion reduction to these hypotheses is kept separate.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace Matrix

variable {d : ℕ}

/-- A level matrix which is globally `n`-dense must live on level at
least `n`, provided there is at least one coordinate. -/
theorem support_ge_of_onLevel_denseAt
    [Nonempty ι]
    {M : Matrix ι d} {n l : ℕ} (hd : 0 < d)
    (hlevel : M.OnLevel l)
    (hdense : M.DenseAt n) :
    n ≤ l := by
  let i0 : Fin d := ⟨0, hd⟩
  let s : Node ι := rayNode (ι := ι) n
  have hs : s ∈ treeLevel (ι := ι) n := by
    dsimp [s, treeLevel]
    exact rayNode_length n
  rcases hdense i0 hs with ⟨z, hzM, hsz⟩
  have hzlen : z.length = l := hlevel i0 z hzM
  have hslen : s.length = n := by
    dsimp [s]
    exact rayNode_length n
  have hlen := hsz.length_le
  rw [hslen, hzlen] at hlen
  exact hlen

/-- Cartesian products preserve global density coordinatewise. -/
theorem snoc_denseAt
    {M : Matrix ι d} {Y : Set (Node ι)} {n : ℕ}
    (hM : M.DenseAt n)
    (hY : HalpernLauchli.DenseAt Y n) :
    (M.snoc Y).DenseAt n := by
  intro i s hs
  cases i using Fin.lastCases with
  | last =>
      simpa [Matrix.snoc] using hY hs
  | cast j =>
      simpa [Matrix.snoc] using hM j hs

end Matrix

/-- State maintained while processing immediate successors of the last-tree
root in the final induction. -/
structure SectionFusionState
    (ι : Type u) (d : ℕ)
    (P : Set (Fin (d + 1) → Node ι)) where
  M : Matrix ι d
  level : ℕ
  Y : Set (Node ι)
  onLevel : M.OnLevel level
  denseOne : M.DenseAt 1
  level_pos : 0 < level
  Y_below : ∀ y ∈ Y, y.length < level
  sections : ∀ y ∈ Y, M.carrier ⊆ lastSection P y

/-- Initial empty fusion state. -/
noncomputable def initialSectionFusionState
    [Nonempty ι]
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι)) :
    SectionFusionState ι d P := {
  M := Matrix.fullLevel 1
  level := 1
  Y := ∅
  onLevel := Matrix.fullLevel_onLevel (ι := ι) (d := d) 1
  denseOne := Matrix.fullLevel_dense (ι := ι) (d := d) 1
  level_pos := by omega
  Y_below := by simp
  sections := by simp
}

/-- The data recorded by one successor-processing step. -/
structure SectionFusionStep
    (ι : Type u) {d : ℕ}
    {P : Set (Fin (d + 1) → Node ι)}
    (S : SectionFusionState ι d P)
    (a : ι) where
  next : SectionFusionState ι d P
  oldY_subset : S.Y ⊆ next.Y
  covers_child :
    ∃ y ∈ next.Y, ([a] : Node ι).IsPrefix y

/-- One section-fusion step exists by Lemma 3.16. -/
theorem exists_sectionFusionStep
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : SectionFusionState ι d P)
    (a : ι) :
    Nonempty (SectionFusionStep ι S a) := by
  classical
  have hchildle : ([a] : Node ι).length ≤ S.level := by
    simp
    have hpos := S.level_pos
    omega
  let t : Node ι := extendToLevel ([a] : Node ι) S.level
  have hchildt : ([a] : Node ι).IsPrefix t := by
    dsimp [t]
    exact prefix_extendToLevel _ _
  rcases lemma316 hd hHDHL hstab hno S.level t with
    ⟨y, N, l, hty, hylt, hNlevel, hNdense, hNsub⟩
  have hSl : S.level ≤ l :=
    N.support_ge_of_onLevel_denseAt hd hNlevel hNdense
  let R : Matrix ι d := S.M.refineOver N
  have hRlevel : R.OnLevel l := by
    dsimp [R]
    exact Matrix.refineOver_onLevel hNlevel
  have hRdense : R.DenseAt 1 := by
    dsimp [R]
    exact Matrix.refineOver_denseAt
      S.onLevel S.denseOne hNdense
  have hRsubN : R.carrier ⊆ N.carrier := by
    dsimp [R]
    exact Matrix.refineOver_carrier_subset_right S.M N
  let Y' : Set (Node ι) := Set.insert y S.Y
  let T : SectionFusionState ι d P := {
    M := R
    level := l
    Y := Y'
    onLevel := hRlevel
    denseOne := hRdense
    level_pos := S.level_pos.trans_le hSl
    Y_below := by
      intro z hz
      rcases hz with rfl | hzOld
      · exact hylt
      · exact (S.Y_below z hzOld).trans_le hSl
    sections := by
      intro z hz
      rcases hz with rfl | hzOld
      · exact hRsubN.trans hNsub
      · dsimp [R]
        exact Matrix.refineOver_preserves_section
          hd hstab S.onLevel hNlevel
          (S.Y_below z hzOld) (S.sections z hzOld)
  }
  refine ⟨{
    next := T
    oldY_subset := ?_
    covers_child := ?_
  }⟩
  · intro z hz
    exact Or.inr hz
  · refine ⟨y, ?_, hchildt.trans hty⟩
    exact Or.inl rfl

/-- Choose one section-fusion step. -/
noncomputable def nextSectionFusionStep
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : SectionFusionState ι d P)
    (a : ι) :
    SectionFusionStep ι S a :=
  Classical.choice
    (exists_sectionFusionStep hd hHDHL hstab hno S a)

/-- Process a finite list of immediate-successor labels. -/
noncomputable def fuseChildrenFrom
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    SectionFusionState ι d P → List ι →
      SectionFusionState ι d P
  | S, [] => S
  | S, a :: as =>
      fuseChildrenFrom hd hHDHL hstab hno
        (nextSectionFusionStep
          hd hHDHL hstab hno S a).next as

/-- Processing more children only enlarges the set of chosen last-coordinate
nodes. -/
theorem fuseChildrenFrom_Y_mono
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : SectionFusionState ι d P)
    (as : List ι) :
    S.Y ⊆ (fuseChildrenFrom
      hd hHDHL hstab hno S as).Y := by
  induction as generalizing S with
  | nil =>
      exact fun _ hz => hz
  | cons a as ih =>
      let step :=
        nextSectionFusionStep
          hd hHDHL hstab hno S a
      have hfirst : S.Y ⊆ step.next.Y :=
        step.oldY_subset
      have hrest :
          step.next.Y ⊆
            (fuseChildrenFrom
              hd hHDHL hstab hno step.next as).Y :=
        ih step.next
      simpa [fuseChildrenFrom, step] using hfirst.trans hrest

/-- Every label occurring in the processed list has a chosen node above its
corresponding immediate successor. -/
theorem fuseChildrenFrom_covers
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (S : SectionFusionState ι d P)
    (as : List ι) {a : ι}
    (ha : a ∈ as) :
    ∃ y ∈ (fuseChildrenFrom
      hd hHDHL hstab hno S as).Y,
      ([a] : Node ι).IsPrefix y := by
  induction as generalizing S with
  | nil =>
      simp at ha
  | cons b bs ih =>
      simp only [List.mem_cons] at ha
      let step :=
        nextSectionFusionStep
          hd hHDHL hstab hno S b
      rcases ha with rfl | haTail
      · rcases step.covers_child with
          ⟨y, hy, hby⟩
        have hmono :
            step.next.Y ⊆
              (fuseChildrenFrom
                hd hHDHL hstab hno step.next bs).Y :=
          fuseChildrenFrom_Y_mono
            hd hHDHL hstab hno step.next bs
        refine ⟨y, ?_, hby⟩
        simpa [fuseChildrenFrom, step] using hmono hy
      · have hcov :=
          ih step.next haTail
        simpa [fuseChildrenFrom, step] using hcov

/-- Process all immediate successors of the root. -/
noncomputable def fusedAllChildren
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    SectionFusionState ι d P := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  exact fuseChildrenFrom
    hd hHDHL hstab hno
    (initialSectionFusionState P)
    Finset.univ.toList

/-- The chosen last-coordinate nodes dominate level one. -/
theorem fusedAllChildren_Y_dense
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    DenseAt
      (fusedAllChildren hd hHDHL hstab hno).Y 1 := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let S0 : SectionFusionState ι d P :=
    initialSectionFusionState P
  let as : List ι := Finset.univ.toList
  change DenseAt
    (fuseChildrenFrom
      hd hHDHL hstab hno S0 as).Y 1
  intro s hs
  have hslen : s.length = 1 := hs
  cases s with
  | nil =>
      simp at hslen
  | cons a tail =>
      have htail : tail = [] := by
        have hzero : tail.length = 0 := by
          simpa using hslen
        simpa using hzero
      subst tail
      have ha : a ∈ as := by
        dsimp [as]
        simp
      rcases fuseChildrenFrom_covers
          hd hHDHL hstab hno S0 as ha with
        ⟨y, hy, hay⟩
      exact ⟨y, hy, hay⟩

/-- Final stabilized induction step: if the complement of `P` has no
somewhere-dense matrix and (*) holds, then `P` contains a 1-dense matrix
in dimension `d+1`. -/
theorem exists_one_dense_of_stabilized
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    ∃ M : Matrix ι (d + 1),
      M.DenseAt 1 ∧ M.carrier ⊆ P := by
  classical
  let S :=
    fusedAllChildren hd hHDHL hstab hno
  let M : Matrix ι (d + 1) :=
    S.M.snoc S.Y
  have hMdense : M.DenseAt 1 := by
    dsimp [M]
    exact Matrix.snoc_denseAt
      S.denseOne
      (fusedAllChildren_Y_dense
        hd hHDHL hstab hno)
  refine ⟨M, hMdense, ?_⟩
  intro z hz
  have hzpair :
      front z ∈ S.M.carrier ∧ last z ∈ S.Y := by
    apply (Matrix.mem_snoc_carrier_appendLast
      S.M S.Y (front z) (last z)).mp
    rw [appendLast_front_last]
    exact hz
  have hsection :
      front z ∈ lastSection P (last z) :=
    S.sections (last z) hzpair.2 hzpair.1
  change appendLast (front z) (last z) ∈ P at hsection
  rw [appendLast_front_last] at hsection
  exact hsection

end HalpernLauchli
end Milliken
