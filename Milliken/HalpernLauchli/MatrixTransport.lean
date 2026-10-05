import Milliken.HalpernLauchli.StabilizationPair

/-!
# Transporting dense matrices through common-level strong embeddings

The Chapter 3 stabilization argument works in a pulled-back product of
strong subtrees.  To return to the original product we need two elementary
transport facts.

* a 1-dense matrix stays 1-dense when every coordinate embedding fixes the
  root;
* a somewhere-dense matrix stays somewhere dense under a common-level
  family of strong embeddings.

The second point uses only the first ambient level above a common image
base.  If a source matrix is dense above `base` at level `n`, first move
each base coordinate to source level `n-1`.  Every immediate successor of
the resulting image base is covered by the corresponding labelled branch of
the strong embedding.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace Matrix

/-- Coordinatewise image of a matrix under a family of strong embeddings. -/
def imageUnder {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (M : Matrix ι d) :
    Matrix ι d where
  coord := fun i => (F i).toFun '' M.coord i

/-- Every point of an image matrix has a simultaneous source point in the
original matrix. -/
theorem exists_source_of_mem_imageUnder
    {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (M : Matrix ι d)
    {z : Fin d → Node ι}
    (hz : z ∈ (M.imageUnder F).carrier) :
    ∃ x ∈ M.carrier, mapTuple F x = z := by
  classical
  choose x hxM hxz using fun i => hz i
  refine ⟨x, ?_, ?_⟩
  · intro i
    exact hxM i
  · funext i
    exact hxz i

/-- A matrix contained in a pullback maps back into the original set. -/
theorem imageUnder_carrier_subset_of_pullback
    {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (M : Matrix ι d)
    (P : Set (Fin d → Node ι))
    (hM : M.carrier ⊆ pullbackProduct F P) :
    (M.imageUnder F).carrier ⊆ P := by
  intro z hz
  rcases exists_source_of_mem_imageUnder F M hz with
    ⟨x, hxM, hxz⟩
  have hxP : mapTuple F x ∈ P := hM hxM
  rwa [hxz] at hxP

/-- Root-fixing strong embeddings preserve global 1-density. -/
theorem imageUnder_denseAt_one
    {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (M : Matrix ι d)
    (hroot : ∀ i, (F i).toFun ([] : Node ι) = [])
    (hM : M.DenseAt 1) :
    (M.imageUnder F).DenseAt 1 := by
  intro i s hs
  change s.length = 1 at hs
  have hchild :
      ∃ a : ι, child ([] : Node ι) a = s :=
    exists_child_eq_of_prefix_length_succ
      (List.nil_prefix) (by simpa using hs)
  rcases hchild with ⟨a, rfl⟩
  have hsourceLevel :
      (child ([] : Node ι) a).length = 1 := by
    simp [child]
  rcases hM i hsourceLevel with
    ⟨y, hyM, hy⟩
  refine ⟨(F i).toFun y, ?_, ?_⟩
  · exact ⟨y, hyM, rfl⟩
  · have hbranch := (F i).branch ([] : Node ι) a
    have hmono := (F i).prefix_mono hy
    simpa [hroot i] using hbranch.trans hmono

/-- A common-level family of strong embeddings sends somewhere-dense
matrices to somewhere-dense matrices.

The source base is first extended to level `n-1`; common levels make all
its images lie on one target level.  Density at source level `n` then
covers every labelled immediate successor of the image base. -/
theorem imageUnder_somewhereDense
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (F : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hF : HasCommonLevels F levels)
    (M : Matrix ι d)
    (hM : M.SomewhereDense) :
    (M.imageUnder F).SomewhereDense := by
  rcases hM with ⟨base, n, hbase, hdense⟩
  let i0 : Fin d := ⟨0, hd⟩
  have hn : 0 < n := by
    have h := hbase i0
    omega
  let r : ℕ := n - 1
  let raised : Fin d → Node ι :=
    fun i => extendToLevel (base i) r
  have hbase_le : ∀ i, (base i).length ≤ r := by
    intro i
    have h := hbase i
    dsimp [r]
    omega
  have hraised : ∀ i, (base i).IsPrefix (raised i) := by
    intro i
    dsimp [raised]
    exact prefix_extendToLevel _ _
  have hraised_len : IsLevelVectorAt r raised := by
    intro i
    dsimp [raised]
    exact length_extendToLevel (hbase_le i)
  let imageBase : Fin d → Node ι :=
    mapTuple F raised
  let q : ℕ := levels r + 1
  refine ⟨imageBase, q, ?_, ?_⟩
  · intro i
    dsimp [imageBase, q, mapTuple]
    rw [hF.2 i, hraised_len i]
    omega
  · intro i s hs
    have himage_len :
        ((F i).toFun (raised i)).length = levels r := by
      rw [hF.2 i, hraised_len i]
    have hslen :
        s.length = ((F i).toFun (raised i)).length + 1 := by
      rw [hs.2, himage_len]
    rcases exists_child_eq_of_prefix_length_succ
        hs.1 hslen with
      ⟨a, ha⟩
    let u : Node ι := child (raised i) a
    have hulen : u.length = n := by
      have hu :
          u.length = (raised i).length + 1 := by
        simp [u, child]
      rw [hu, hraised_len i]
      dsimp [r]
      omega
    have hbaseu : (base i).IsPrefix u :=
      (hraised i).trans (List.prefix_append _ _)
    rcases hdense i
        (show u ∈ coneLevel (base i) n from
          ⟨hbaseu, hulen⟩) with
      ⟨y, hyM, huy⟩
    refine ⟨(F i).toFun y, ?_, ?_⟩
    · exact ⟨y, hyM, rfl⟩
    · rw [← ha]
      exact
        ((F i).branch (raised i) a).trans
          ((F i).prefix_mono huy)

end Matrix

/-- Pullback through a common-level family preserves the property that the
complement contains no somewhere-dense matrix. -/
theorem no_somewhereDense_compl_pullbackProduct
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (F : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hF : HasCommonLevels F levels)
    (P : Set (Fin d → Node ι))
    (hno : ¬ ContainsSomewhereDense Pᶜ) :
    ¬ ContainsSomewhereDense (pullbackProduct F P)ᶜ := by
  rintro ⟨M, hMsome, hMsub⟩
  let N : Matrix ι d := M.imageUnder F
  have hNsome : N.SomewhereDense := by
    dsimp [N]
    exact Matrix.imageUnder_somewhereDense
      hd F levels hF M hMsome
  have hNsub : N.carrier ⊆ Pᶜ := by
    intro z hzN hzP
    rcases Matrix.exists_source_of_mem_imageUnder
        F M hzN with
      ⟨x, hxM, hxz⟩
    have hxnot : x ∈ (pullbackProduct F P)ᶜ :=
      hMsub hxM
    apply hxnot
    change mapTuple F x ∈ P
    rwa [hxz]
  exact hno ⟨N, hNsome, hNsub⟩

end HalpernLauchli
end Milliken
