import Milliken.GeneralTree.HeterogeneousWedgeComponentCones
import Milliken.GeneralTree.HeterogeneousCompressionTransport

/-!
# Matrix transport between compressed heterogeneous trees and a common wedge

This applies the checked strong-cone construction to *full* compressed
source trees. Each coordinate has a different node type and arbitrary
locally finite degree. A fresh common-root wedge puts all coordinates
in one ambient without altering their source frontiers.

The two coordinatewise directions are:
* lift an original product colour set to wedge tuples, and
* pull back a wedge matrix to the dependent compressed-node matrix.

For both density and monochromaticity, use the original general-tree
source-level and order correspondences instead of a homogeneous
alphabet. No Ramsey hypothesis is used in this module.
-/

namespace Milliken
namespace GeneralTree

open CompressedSourceSelection

namespace HeterogeneousCompressionWedge

variable {U : AmbientTree} {d : ℕ}

/-- Genuinely different full compressed ambient factors, one per
coordinate, with all nodes at each selected source frontier. -/
noncomputable def factors
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection) : Fin d → AmbientTree :=
  fun i => compressedAmbientTree (P i) f

/-- The common-root ambient built from every compressed coordinate. -/
noncomputable def ambient
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d) : AmbientTree :=
  WedgeNode.ambientTree (factors P f) hd

/-- Synchronized strong factor family in the common wedge.
This reuses the checked identityStrongSubtree/coneStrong combination. -/
noncomputable def strong
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d) :
    Fin d → StrongSubtree (ambient P f hd) :=
  WedgeNode.componentStrong (factors P f) hd

/-- Encode one fully compressed coordinate as its corresponding
tagged node of the common wedge. -/
noncomputable def tag
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (i : Fin d) (z : Node (P i) f) :
    ambient P f hd :=
  WedgeNode.embed (factors P f) i z

/-- Every original compressed node is on the correct source level
of the synchronized strong component. -/
theorem tag_mem_sourceLevel
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (i : Fin d) (n : ℕ)
    (z : Node (P i) f) (hn : z.fst = n) :
    tag P f hd i z ∈ (strong P f hd i).sourceLevel n := by
  have hzLevel :
      ((factors P f) i).level z = n := by
    change (compressedAmbientTree (P i) f).level z = n
    rw [compressedAmbient_level_eq_index]
    exact hn
  change WedgeNode.embed (factors P f) i z ∈
    (WedgeNode.componentStrong (factors P f) hd i).sourceLevel n
  exact (WedgeNode.mem_componentStrong_sourceLevel_iff
    (factors P f) hd i n _).mpr ⟨z, hzLevel, rfl⟩

/-- A point in the i-th wedge factor is a tagged full-compressed
node, with no other coordinate or new-root points. -/
theorem exists_tag_of_mem
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (i : Fin d) (z : ambient P f hd)
    (hz : z ∈ (strong P f hd i).carrier) :
    ∃ w : Node (P i) f, tag P f hd i w = z := by
  change z ∈ (WedgeNode.componentStrong (factors P f) hd i).carrier at hz
  exact WedgeNode.exists_embed_of_mem_componentStrong
    (factors P f) hd i z hz

/-- Injectivity on one tag follows from the natural Sigma inclusion. -/
theorem tag_injective
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (i : Fin d) :
    Function.Injective (tag P f hd i) := by
  intro x y h
  have hs : (⟨i, x⟩ : Σ j, (factors P f) j) =
      (⟨i, y⟩ : Σ j, (factors P f) j) :=
    WithBot.coe_injective h
  exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2

/-- The common selected ambient map is n ↦ n+1. -/
theorem strong_levels
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d) (i : Fin d) :
    (strong P f hd i).levels = (fun n : ℕ => n + 1) :=
  WedgeNode.componentStrong_levels (factors P f) hd i

/-- Tag a dependent tuple of compressed nodes into one ordinary
product tuple in the common ambient. -/
noncomputable def tagTuple
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (z : (i : Fin d) → Node (P i) f) :
    Fin d → ambient P f hd :=
  fun i => tag P f hd i (z i)

/-- Test the original colour after decoding a correctly tagged tuple.
For tuples outside the intended component product, the test is false;
that convention has no effect on matrices inside the strong family. -/
noncomputable def liftedColour
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (Q : Set (Fin d → U)) :
    Set (Fin d → ambient P f hd) :=
  {z | ∃ x : (i : Fin d) → Node (P i) f,
    (∀ i, tag P f hd i (x i) = z i) ∧
      (fun i => nodeValue (P i) f (x i)) ∈ Q}

/-- Pull back coordinate sets of a wedge product matrix along the
tagged full-compression maps. -/
noncomputable def decodeMatrix
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd)) :
    HeterogeneousCompressedMatrix P f where
  coord := fun i => {z | tag P f hd i z ∈ N.coord i}

/-- Cartesian carrier membership is preserved exactly by tagging. -/
theorem decodeMatrix_carrier_iff
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (z : (i : Fin d) → Node (P i) f) :
    z ∈ (decodeMatrix P f hd N).carrier ↔
      tagTuple P f hd z ∈ N.carrier := Iff.rfl

/-- The set of source tuples is an actual subset of the wedge lifted
colour class when its original decoding has the desired colour. -/
theorem tagTuple_mem_liftedColour
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (Q : Set (Fin d → U))
    (z : (i : Fin d) → Node (P i) f)
    (hz : (fun i => nodeValue (P i) f (z i)) ∈ Q) :
    tagTuple P f hd z ∈ liftedColour P f hd Q :=
  ⟨z, (fun _ => rfl), hz⟩

/-- Monochromatic wedge matrices pull back to the precise original
colour set, using only injectivity of each tagged coordinate. -/
theorem decodeMatrix_carrier_subset_pullback
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (Q : Set (Fin d → U))
    (hN : N.carrier ⊆ liftedColour P f hd Q) :
    (decodeMatrix P f hd N).carrier ⊆
      HeterogeneousCompressedMatrix.pullback P f Q := by
  intro z hz
  have hTuple : tagTuple P f hd z ∈ N.carrier :=
    (decodeMatrix_carrier_iff P f hd N z).mp hz
  obtain ⟨w, hTag, hwQ⟩ := hN hTuple
  have hwz : w = z := by
    funext i
    apply tag_injective P f hd i
    exact hTag i
  change (fun i => nodeValue (P i) f (z i)) ∈ Q
  rwa [hwz] at hwQ

/-- The original matrix from a wedge monochromatic matrix remains
monochromatic under full compressed-level decoding. -/
theorem decodeMatrix_original_subset
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (Q : Set (Fin d → U))
    (hN : N.carrier ⊆ liftedColour P f hd Q) :
    (decodeMatrix P f hd N).original.carrier ⊆ Q :=
  (decodeMatrix P f hd N).original_carrier_subset Q
    (decodeMatrix_carrier_subset_pullback P f hd N Q hN)

/-- Strong-family density in the wedge implies density on each
complete compressed source level, with no thinning of frontiers. -/
theorem decodeMatrix_denseAt
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (n : ℕ) (hN : N.DenseAt n) :
    (decodeMatrix P f hd N).DenseAt n := by
  intro i x
  let z : Node (P i) f := ⟨n, x⟩
  have hz : tag P f hd i z ∈ (strong P f hd i).sourceLevel n :=
    tag_mem_sourceLevel P f hd i n z rfl
  obtain ⟨y, hyN, hzy⟩ := hN i _ hz
  obtain ⟨w, hwy⟩ :=
    exists_tag_of_mem P f hd i y (N.coord_sub i hyN)
  refine ⟨w, ?_, ?_⟩
  · change tag P f hd i w ∈ N.coord i
    rw [hwy]
    exact hyN
  · have hzw : tag P f hd i z ≤ tag P f hd i w := by
      rw [hwy]
      exact hzy
    exact (WedgeNode.embed_le_embed_iff (factors P f) i z w).mp hzw

/-- Consequently the original matrix is dense at the old selected
source index f(n), even when the selection skips many levels. -/
theorem decodeMatrix_original_denseAt
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (hd : 0 < d)
    (N : HeterogeneousMatrix (strong P f hd))
    (n : ℕ) (hN : N.DenseAt n) :
    (decodeMatrix P f hd N).original.DenseAt (f.indices n) :=
  (decodeMatrix P f hd N).original_denseAt
    (decodeMatrix_denseAt P f hd N n hN)

end HeterogeneousCompressionWedge
end GeneralTree
end Milliken
