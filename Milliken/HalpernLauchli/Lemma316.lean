import Milliken.HalpernLauchli.Lemma316Fill

/-!
# Lemma 3.16

This file completes the main finite-Halpern--Läuchli step on page 56 of
Todorčević's proof.

The tower from Lemma 3.15 supplies selected levels `n₀<n₁<...` and decreasing
sets `X₀⊇X₁⊇...`.  We apply finite Halpern--Läuchli on precisely those sparse
levels.  A color-one sparse somewhere-dense matrix contradicts property (4)
after completing it outside its base cones.  Hence the color-zero alternative
survives and gives the required dense section.

The tail normalization introduced in the formalization of Lemma 3.15
disappears at the end because the chosen matrix lies on a level strictly
above the selected last-coordinate node.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace Matrix

variable {d : ℕ}

/-- If every coordinate of `A` is nonempty, containment of product
carriers in a level matrix forces `A` itself to lie on that level. -/
theorem onLevel_of_carrier_subset_of_coord_nonempty
    (A B : Matrix ι d) {l : ℕ}
    (hsub : A.carrier ⊆ B.carrier)
    (hB : B.OnLevel l)
    (hne : ∀ i, (A.coord i).Nonempty) :
    A.OnLevel l := by
  classical
  intro i z hz
  choose w hw using hne
  let x : Fin d → Node ι := Function.update w i z
  have hxA : x ∈ A.carrier := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [x] using hz
    · simpa [x, hji] using hw j
  have hxB : x ∈ B.carrier := hsub hxA
  have hxlen := hB i (x i) (hxB i)
  simpa [x] using hxlen

/-- Global density makes every coordinate nonempty. -/
theorem coord_nonempty_of_denseAt
    [Nonempty ι]
    (M : Matrix ι d) {n : ℕ}
    (hM : M.DenseAt n) :
    ∀ i, (M.coord i).Nonempty := by
  intro i
  let s : Node ι := rayNode (ι := ι) n
  have hs : s ∈ treeLevel (ι := ι) n := by
    dsimp [s, treeLevel]
    exact rayNode_length n
  rcases hM i hs with ⟨y, hy, hsy⟩
  exact ⟨y, hy⟩

/-- Density above a base makes every coordinate nonempty as soon as the base
lies no higher than the target level. -/
theorem coord_nonempty_of_denseAbove
    [Nonempty ι]
    (M : Matrix ι d) (base : Fin d → Node ι) {n : ℕ}
    (hM : M.DenseAbove base n)
    (hbase : ∀ i, (base i).length ≤ n) :
    ∀ i, (M.coord i).Nonempty := by
  intro i
  let s : Node ι := extendToLevel (base i) n
  have hslen : s.length = n := by
    dsimp [s]
    exact length_extendToLevel (hbase i)
  have hs : s ∈ coneLevel (base i) n :=
    ⟨by
      dsimp [s]
      exact prefix_extendToLevel _ _,
      hslen⟩
  rcases hM i hs with ⟨y, hy, hsy⟩
  exact ⟨y, hy⟩

end Matrix

/-- Strict monotonicity reflects order on natural-number indices. -/
theorem index_le_of_strictMono_level_le
    {f : ℕ → ℕ} (hf : StrictMono f)
    {p q : ℕ} (h : f p ≤ f q) :
    p ≤ q := by
  by_contra hpq
  have hqp : q < p := Nat.lt_of_not_ge hpq
  have hlt := hf hqp
  omega

/-- Todorčević's Lemma 3.16, with the supporting matrix level made explicit.

Under the standing induction hypotheses, above every last-coordinate node
`t` and for every target density `k`, there is a later node `y` and a
level matrix `M` whose level is strictly above `y`, which is `k`-dense
and is contained in the original section `P_y`. -/
theorem lemma316
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hHDHL : HDHL ι d)
    (hstab : Stabilized P)
    (hno : ¬ ContainsSomewhereDense Pᶜ)
    (k : ℕ) (t : Node ι) :
    ∃ y : Node ι, ∃ M : Matrix ι d, ∃ l : ℕ,
      t.IsPrefix y ∧
      y.length < l ∧
      M.OnLevel l ∧
      M.DenseAt k ∧
      M.carrier ⊆ lastSection P y := by
  classical
  let levels : ℕ → ℕ :=
    fun p => (lemma316Tower hd hstab hno k t p).n
  have hlevels : StrictMono levels := by
    dsimp [levels]
    exact lemma316Tower_levels_strictMono
      hd hstab hno k t
  have hunbounded :
      ∀ r : ℕ, ∃ q : ℕ, r ≤ levels q := by
    dsimp [levels]
    exact lemma316Tower_levels_unbounded
      hd hstab hno k t
  have hk0 : 0 < levels 0 := by
    dsimp [levels]
    have hpos : 0 < t.length + 1 := by omega
    exact hpos.trans_le (Nat.le_max_right _ _)
  have hk_le_zero : k ≤ levels 0 := by
    dsimp [levels]
    exact lemma316Tower_target_le_zero
      hd hstab hno k t
  rcases sparseFiniteHL_of_hdhl
      hHDHL hk0 hlevels hunbounded with
    ⟨L, hfinite⟩
  rcases hunbounded L with ⟨p, hLp⟩
  let Full : Matrix ι d := Matrix.fullLevel (levels p)
  have hFullDense : Full.DenseAt (levels p) := by
    dsimp [Full]
    exact Matrix.fullLevel_dense (ι := ι) (d := d) (levels p)
  have hFullL : Full.DenseAt L := by
    exact Full.denseAt_of_le hLp hFullDense
  let S := lemma316Tower hd hstab hno k t p
  let y : Node ι := S.sample
  have hyX : y ∈ S.X := by
    dsimp [y, S]
    exact (lemma316Tower hd hstab hno k t p).sample_mem
  have hybelow : y.length < levels p := by
    dsimp [y, S, levels]
    exact (lemma316Tower hd hstab hno k t p).sample_below
  have hyt : t.IsPrefix y := by
    have hyX0 :
        y ∈ (lemma316Tower hd hstab hno k t 0).X := by
      have hsub :=
        lemma316Tower_X_antitone
          hd hstab hno k t (p := 0) (q := p) (Nat.zero_le p)
      exact hsub hyX
    rw [lemma316Tower_zero_X] at hyX0
    exact hyX0
  let K0 : Set (Fin d → Node ι) :=
    lastSection (tailNormalize P) y
  rcases hfinite Full hFullL K0 with hone | hzero
  · rcases hone with ⟨N, hNsparse, hNsub⟩
    rcases hNsparse with ⟨q, base, hbase, hNdense⟩
    have hbaseLt :
        ∀ i, (base i).length < levels (q + 1) := by
      intro i
      rw [hbase i]
      exact hlevels (Nat.lt_succ_self q)
    have hNnonempty :
        ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAbove base hNdense
        (fun i => Nat.le_of_lt (hbaseLt i))
    have hNsubFull : N.carrier ⊆ Full.carrier := by
      intro z hz
      exact (hNsub hz).1
    have hNlevel : N.OnLevel (levels p) := by
      apply N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
      · dsimp [Full]
        exact Matrix.fullLevel_onLevel (ι := ι) (d := d) (levels p)
      · exact hNnonempty
    have hnextle : levels (q + 1) ≤ levels p := by
      let i0 : Fin d := ⟨0, hd⟩
      let s : Node ι :=
        extendToLevel (base i0) (levels (q + 1))
      have hslen : s.length = levels (q + 1) := by
        dsimp [s]
        exact length_extendToLevel
          (Nat.le_of_lt (hbaseLt i0))
      have hscone :
          s ∈ coneLevel (base i0) (levels (q + 1)) :=
        ⟨by
          dsimp [s]
          exact prefix_extendToLevel _ _,
          hslen⟩
      rcases hNdense i0 hscone with
        ⟨z, hzN, hsz⟩
      have hzlen : z.length = levels p :=
        hNlevel i0 z hzN
      have hlen := hsz.length_le
      rw [hslen, hzlen] at hlen
      exact hlen
    have hindex : q + 1 ≤ p :=
      index_le_of_strictMono_level_le hlevels hnextle
    have hyNext :
        y ∈ (lemma316Tower hd hstab hno k t (q + 1)).X := by
      have hsub :=
        lemma316Tower_X_antitone
          hd hstab hno k t
          (p := q + 1) (q := p) hindex
      exact hsub hyX
    let A : Matrix ι d :=
      N.fillOutsideAbove base (levels p)
    have hAlevel :
        A.LevelDenseAt (levels (q + 1)) := by
      dsimp [A]
      exact N.fillOutsideAbove_levelDenseAt
        base hNlevel hNdense hbaseLt hnextle
    have hgood :
        SectionsGoodAt (tailNormalize P)
          (levels q) (levels (q + 1))
          (lemma316Tower hd hstab hno k t (q + 1)).X := by
      dsimp [levels]
      exact lemma316Tower_good
        hd hstab hno k t q
    have hprod :
        ProductDenseAt
          (lastSection (tailNormalize P) y ∩ A.carrier)
          (levels q) :=
      hgood y hyNext A hAlevel
    rcases hprod base hbase with
      ⟨z, hz, hpref⟩
    have hzN : z ∈ N.carrier := by
      dsimp [A] at hz
      exact N.carrier_mem_of_fillOutsideAbove_of_prefix
        base hz.2 hpref
    have hzCompl : z ∈ K0ᶜ :=
      (hNsub hzN).2
    have hzK0 : z ∈ K0 := by
      exact hz.1
    exact False.elim (hzCompl hzK0)
  · rcases hzero with ⟨N, hNdense0, hNsub⟩
    have hNnonempty :
        ∀ i, (N.coord i).Nonempty :=
      N.coord_nonempty_of_denseAt hNdense0
    have hNsubFull : N.carrier ⊆ Full.carrier := by
      intro z hz
      exact (hNsub hz).1
    have hNlevel : N.OnLevel (levels p) := by
      apply N.onLevel_of_carrier_subset_of_coord_nonempty
        Full hNsubFull
      · dsimp [Full]
        exact Matrix.fullLevel_onLevel (ι := ι) (d := d) (levels p)
      · exact hNnonempty
    have hNdense : N.DenseAt k :=
      N.denseAt_of_le hk_le_zero hNdense0
    have hNsubP :
        N.carrier ⊆ lastSection P y := by
      intro z hzN
      have hzK0 : z ∈ K0 :=
        (hNsub hzN).2
      have hzLevel :
          IsLevelVectorAt (levels p) z := by
        intro i
        exact hNlevel i (z i) (hzN i)
      have hiff :=
        mem_lastSection_tailNormalize_of_above
          hd P y z hzLevel hybelow
      change z ∈ lastSection (tailNormalize P) y at hzK0
      exact hiff.mp hzK0
    exact ⟨y, N, levels p, hyt, hybelow,
      hNlevel, hNdense, hNsubP⟩

end HalpernLauchli
end Milliken
