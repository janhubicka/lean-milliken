import Milliken.GeneralTree.CompressedSourceOrder
import Milliken.GeneralTree.HeterogeneousRestrictedReduction

/-!
# Transport of heterogeneous matrices through full source-level compression

For every coordinate strong tree, keep *all* nodes on the selected
source levels. Unlike strong thinning this transport preserves exactly
the full selected frontier, which is essential to Remark 3.8.

This module does not assume a common compressed ambient tree.
Matrices are expressed directly on the (possibly non-isomorphic)
coordinate compressed-node types, and mapped into the original
heterogeneous matrix language. It proves both density transport and
the complementary somewhere-density obstruction needed for the
subsequence-to-original HDHL reduction.

No global bound on branching is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

open CompressedSourceSelection

/-- Coordinatewise sets of nodes in the full (not thinned) compressed
trees, whose coordinate node types may depend on the index i. -/
structure HeterogeneousCompressedMatrix
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection) where
  coord : (i : Fin d) → Set (Node (P i) f)

namespace HeterogeneousCompressedMatrix

variable {P : Fin d → StrongSubtree U}
variable {f : CompressedSourceSelection}

/-- Cartesian product carrier, with its actual dependent node types. -/
def carrier (M : HeterogeneousCompressedMatrix P f) :
    Set ((i : Fin d) → Node (P i) f) :=
  {x | ∀ i, x i ∈ M.coord i}

/-- Density above the entire full compressed source level n. -/
def DenseAt (M : HeterogeneousCompressedMatrix P f) (n : ℕ) : Prop :=
  ∀ i : Fin d, ∀ x : NodeAt (P i) f n,
    ∃ y : Node (P i) f, y ∈ M.coord i ∧
      (⟨n, x⟩ : Node (P i) f) ≤ y

/-- The corresponding original-coordinate matrix, using the original
actual ambient nodes. -/
def original (M : HeterogeneousCompressedMatrix P f) :
    HeterogeneousMatrix P where
  coord := fun i => (nodeValue (P i) f) '' M.coord i
  coord_sub := by
    intro i x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact z.2.2.1

/-- Each original selected-source node becomes exactly one compressed
node. Thus denseAt in the full compression implies density at the
selected source index back in the original trees. -/
theorem original_denseAt
    (M : HeterogeneousCompressedMatrix P f)
    {n : ℕ} (hM : M.DenseAt n) :
    M.original.DenseAt (f.indices n) := by
  intro i x hx
  let a : Node (P i) f := ⟨n, ⟨x, hx⟩⟩
  obtain ⟨b, hb, hab⟩ := hM i ⟨x, hx⟩
  refine ⟨nodeValue (P i) f b, ⟨b, hb, rfl⟩, ?_⟩
  exact (node_le_iff (P i) f a b).mp hab

/-- Pull back a colour class in the old heterogeneous product along
the injective map from each fully compressed coordinate. -/
def pullback
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (Q : Set (Fin d → U)) :
    Set ((i : Fin d) → Node (P i) f) :=
  {x | (fun i => nodeValue (P i) f (x i)) ∈ Q}

/-- Decode each original product point of an image matrix as the
pointwise image of a tuple of genuine compressed nodes. -/
theorem original_mem_iff
    (M : HeterogeneousCompressedMatrix P f)
    (x : Fin d → U) :
    x ∈ M.original.carrier ↔
      ∃ y : (i : Fin d) → Node (P i) f,
        y ∈ M.carrier ∧
          ∀ i, nodeValue (P i) f (y i) = x i := by
  classical
  constructor
  · intro hx
    have hchoose (i : Fin d) :
        ∃ y : Node (P i) f,
          y ∈ M.coord i ∧ nodeValue (P i) f y = x i := by
      obtain ⟨y, hy, hval⟩ := hx i
      exact ⟨y, hy, hval⟩
    let y : (i : Fin d) → Node (P i) f :=
      fun i => Classical.choose (hchoose i)
    refine ⟨y, ?_, ?_⟩
    · intro i
      exact (Classical.choose_spec (hchoose i)).1
    · intro i
      exact (Classical.choose_spec (hchoose i)).2
  · rintro ⟨y, hy, hval⟩
    intro i
    exact ⟨y i, hy i, hval i⟩

/-- Monochromaticity of a matrix in the fully compressed product
transports to the uncompressed original product. -/
theorem original_carrier_subset
    (M : HeterogeneousCompressedMatrix P f)
    (Q : Set (Fin d → U))
    (hSub : M.carrier ⊆ pullback P f Q) :
    M.original.carrier ⊆ Q := by
  intro x hx
  obtain ⟨y, hy, heq⟩ := (original_mem_iff M x).mp hx
  have h := hSub hy
  have hfun : (fun i => nodeValue (P i) f (y i)) = x :=
    funext heq
  simpa only [pullback, Set.mem_setOf_eq, hfun] using h

/-- Density in cones between two (possibly widely separated)
compressed source indices. The compressed bases are actual nodes
and all compressed nodes of the target full level are tested. -/
def SomewhereDense
    (M : HeterogeneousCompressedMatrix P f) : Prop :=
  ∃ p q : ℕ, p < q ∧
    ∃ base : (i : Fin d) → Node (P i) f,
      (∀ i, (base i).fst = p) ∧
      ∀ i (z : Node (P i) f), z.fst = q →
        base i ≤ z →
          ∃ y : Node (P i) f,
            y ∈ M.coord i ∧ z ≤ y

/-- A somewhere-dense compressed matrix becomes a matrix somewhere
dense *between the selected source indices* in the original product.
This is the exact direction used to transfer absence of a
complementary obstruction through full compression. -/
theorem original_restricted_somewhereDense
    (M : HeterogeneousCompressedMatrix P f)
    (hM : M.SomewhereDense) :
    HeterogeneousRestrictedSomewhereDense P f.indices M.original := by
  classical
  obtain ⟨p, q, hpq, base, hbase, hDense⟩ := hM
  let B : HeterogeneousLevelTuple P (f.indices p) :=
    ⟨(fun i => nodeValue (P i) f (base i)), by
      intro i
      have hi : (base i).fst = p := hbase i
      have hs := (base i).snd.property
      change (base i).2.1 ∈ (P i).sourceLevel (f.indices p)
      simpa only [hi] using hs⟩
  refine ⟨p, q, hpq, B, ?_⟩
  intro i x hx hbx
  let a : Node (P i) f := ⟨q, ⟨x, hx⟩⟩
  have hba : base i ≤ a :=
    (node_le_iff (P i) f (base i) a).mpr hbx
  obtain ⟨y, hy, hay⟩ := hDense i a rfl hba
  refine ⟨nodeValue (P i) f y, ⟨y, hy, rfl⟩, ?_⟩
  exact (node_le_iff (P i) f a y).mp hay

/-- No matrix in the compressed complementary colour can be
somewhere dense if the original complement has no matrix dense
between the selected full source levels. -/
theorem no_compressed_complement
    (P : Fin d → StrongSubtree U)
    (f : CompressedSourceSelection)
    (Q : Set (Fin d → U))
    (hno :
      ¬ HeterogeneousContainsRestrictedSomewhereDense
        P f.indices Qᶜ)
    (M : HeterogeneousCompressedMatrix P f)
    (hM : M.SomewhereDense)
    (hBad : M.carrier ⊆ pullback P f Qᶜ) :
    False := by
  apply hno
  refine ⟨M.original, M.original_restricted_somewhereDense hM, ?_⟩
  exact M.original_carrier_subset Qᶜ hBad

end HeterogeneousCompressedMatrix
end GeneralTree
end Milliken
