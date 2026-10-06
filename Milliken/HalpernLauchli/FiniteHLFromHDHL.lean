import Milliken.HalpernLauchli.FiniteHLTransport

/-!
# Finite Halpern--Läuchli from HDHL by compactness

The finite subcover of the binary-coloring space gives finitely many finite
witness matrices.  Let `l` dominate the target density `k` and every node
appearing in those witnesses.

Given an arbitrary `l`-dense ambient matrix `M`, extend every node of the
full product into `M` coordinatewise.  Pull a local coloring of `M` back
along this extension map.  One of the finitely many witness cylinders is
monochromatic for the pulled-back coloring; transporting that witness into
`M` gives exactly the finite Halpern--Läuchli dichotomy.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Todorčević's finite Halpern--Läuchli theorem (Theorem 3.9), as a
compactness consequence of `HDHL_d`. -/
theorem finiteHL_of_hdhl
    [Finite ι] [Nonempty ι]
    {d : ℕ}
    (hHDHL : HDHL ι d) :
    FiniteHL ι d := by
  classical
  intro k
  rcases exists_finiteHLWitness_subcover
      (ι := ι) (d := d) (k := k) hHDHL with
    ⟨F, hcover⟩
  let L : ℕ := finiteWitnessFamilyBound F
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
    have hL :
        s.length ≤ L := by
      dsimp [L]
      exact witness_length_le_familyBound hWF hs
    dsimp [l]
    exact hL.trans (Nat.le_max_right _ _)
  let N : Matrix ι d := transportWitness W M hM
  have hNsubM : N.carrier ⊆ M.carrier := by
    dsimp [N]
    exact transportWitness_subset W M hM
  rcases W.shape with hzero | hone
  · right
    rcases hzero with ⟨hcolor, hWdense⟩
    have hNdense : N.DenseAt k := by
      dsimp [N]
      exact transportWitness_dense W M hM hbound hWdense
    refine ⟨N, hNdense, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    rcases exists_source_of_mem_transportWitness
        W M hM hz with
      ⟨x, hxW, hxmap⟩
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
    rcases hone with ⟨hcolor, hWsome⟩
    have hNsome : N.SomewhereDense := by
      dsimp [N]
      exact transportWitness_somewhereDense W M hM hbound hWsome
    refine ⟨N, hNsome, ?_⟩
    intro z hz
    refine ⟨hNsubM hz, ?_⟩
    intro hzK
    rcases exists_source_of_mem_transportWitness
        W M hM hz with
      ⟨x, hxW, hxmap⟩
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
