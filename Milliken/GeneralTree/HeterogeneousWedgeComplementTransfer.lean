import Milliken.GeneralTree.HeterogeneousWedgeCompressionTransport
import Milliken.GeneralTree.HeterogeneousIdentityBridge

/-!
# Excluding complementary somewhere-dense matrices after full compression

The checked reduced heterogeneous HDHL induction works for a single
ambient and excludes **ordinary** somewhere-dense complementary
matrices. Todorčević Remark 3.8 gives only the corresponding
**restricted selected-level** exclusion.

The exact bridge is:

1. Put all full compressed coordinate trees into the common-root
   wedge and use the already checked coneStrong components.
2. Align different base levels of a hypothetical somewhere-dense
   wedge matrix to a common penultimate source level, using the
   checked identity-selection lemma.
3. Decode its coordinate matrix to the full compressed node types,
   preserving density above the synchronized source-level base.
4. Apply the already checked transport of compressed somewhere
   density into restricted somewhere density in the original trees.

No homogeneous alphabet, bounded degree or new Ramsey hypothesis
occurs in this transport.
-/

namespace Milliken
namespace GeneralTree

open CompressedSourceSelection

namespace HeterogeneousCompressionWedge

variable {U : AmbientTree} {d : ℕ}

/-- An ordinary somewhere-dense matrix in the common wedge becomes a
somewhere-dense full-compressed matrix with one common selected
base index. This uses the *checked* identity-level alignment lemma. -/
theorem decodeMatrix_somewhereDense
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (hN : N.SomewhereDense) :
    (decodeMatrix P f hd N).SomewhereDense := by
  classical
  obtain ⟨p, q, hpq, b, hDense⟩ :=
    heterogeneousSomewhereDense_to_restricted_id
      (strong P f hd) hd N hN
  have hex (i : Fin d) :
      ∃ z : CompressedSourceSelection.Node (P i) f,
        z.fst = p ∧ tag P f hd i z = b.1 i := by
    have hbi : b.1 i ∈ (strong P f hd i).sourceLevel p :=
      b.2 i
    have hbi' :
        b.1 i ∈
          (WedgeNode.componentStrong (factors P f) hd i).sourceLevel p :=
      hbi
    obtain ⟨z, hzlev, hzTag⟩ :=
      (WedgeNode.mem_componentStrong_sourceLevel_iff
        (factors P f) hd i p (b.1 i)).mp hbi'
    have hzRank : z.fst = p := by
      change (compressedAmbientTree (P i) f).level z = p at hzlev
      rw [compressedAmbient_level_eq_index] at hzlev
      exact hzlev
    exact ⟨z, hzRank, hzTag⟩
  let beta : (i : Fin d) → CompressedSourceSelection.Node (P i) f :=
    fun i => Classical.choose (hex i)
  have hbetaRank (i : Fin d) :
      (beta i).fst = p :=
    (Classical.choose_spec (hex i)).1
  have hbetaTag (i : Fin d) :
      tag P f hd i (beta i) = b.1 i :=
    (Classical.choose_spec (hex i)).2
  refine ⟨p, q, hpq, beta, hbetaRank, ?_⟩
  intro i z hzq hbetaz
  have hzSource :
      tag P f hd i z ∈ (strong P f hd i).sourceLevel q :=
    tag_mem_sourceLevel P f hd i q z hzq
  have hbBelow : b.1 i ≤ tag P f hd i z := by
    rw [← hbetaTag i]
    exact (WedgeNode.embed_le_embed_iff
      (factors P f) i (beta i) z).mpr hbetaz
  obtain ⟨y, hyN, hzy⟩ :=
    hDense i (tag P f hd i z) hzSource hbBelow
  obtain ⟨w, hwy⟩ :=
    exists_tag_of_mem P f hd i y (N.coord_sub i hyN)
  refine ⟨w, ?_, ?_⟩
  · change tag P f hd i w ∈ N.coord i
    rw [hwy]
    exact hyN
  · have hzBelow : tag P f hd i z ≤ tag P f hd i w := by
      rw [hwy]
      exact hzy
    exact (WedgeNode.embed_le_embed_iff
      (factors P f) i z w).mp hzBelow

/-- A restricted complementary obstruction in the original family
is exactly what would be produced by any ordinary somewhere-dense
complementary matrix in the synchronized full-compressed wedge. -/
theorem no_wedge_complement_somewhereDense
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (Q : Set (Fin d → U))
    (hno :
      ¬ HeterogeneousContainsRestrictedSomewhereDense
        P f.indices Qᶜ) :
    ¬ HeterogeneousContainsSomewhereDense
      (strong P f hd) (liftedColour P f hd Q)ᶜ := by
  rintro ⟨N, hNsome, hNbad⟩
  let M : HeterogeneousCompressedMatrix P f :=
    decodeMatrix P f hd N
  have hMsome : M.SomewhereDense :=
    decodeMatrix_somewhereDense P f hd N hNsome
  have hMbad :
      M.carrier ⊆
        HeterogeneousCompressedMatrix.pullback P f Qᶜ := by
    intro z hz
    change (fun i => nodeValue (P i) f (z i)) ∈ Qᶜ
    intro hQ
    have hzW : tagTuple P f hd z ∈ N.carrier :=
      (decodeMatrix_carrier_iff P f hd N z).mp hz
    exact (hNbad hzW)
      (tagTuple_mem_liftedColour P f hd Q z hQ)
  exact HeterogeneousCompressedMatrix.no_compressed_complement
    P f Q hno M hMsome hMbad

end HeterogeneousCompressionWedge
end GeneralTree
end Milliken
