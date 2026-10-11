import Milliken.HalpernLauchli.HalesJewettBridge

/-!
# Application-facing synchronized vector Halpern–Läuchli

The checked Hales–Jewett bridge gives a vector of independent
homogeneous-tree strong embeddings with ONE common level map.
Homogeneity is for common-level node tuples, NOT for finite vector
strong-subtree approximations. The latter is a separate Milliken theorem.
-/

namespace Milliken
namespace Applications

universe u

/-- One synchronized family of independent strong embeddings of
the homogeneous tree `ι^{<ω}`. -/
structure HomogeneousVectorStrongEmbedding
    (ι : Type u) (d : ℕ) where
  coordinate : Fin d → StrongEmbedding ι
  levels : ℕ → ℕ
  commonLevels : HalpernLauchli.HasCommonLevels coordinate levels

/-- Verified strong-subtree Halpern–Läuchli in arbitrary finite dimension,
packaged as a synchronized vector of strong embeddings rather than an
unstructured function family. -/
theorem homogeneousVectorHalpernLauchli
    {ι : Type u} [Finite ι] [Nonempty ι]
    (d colors : ℕ) [NeZero colors]
    (colour : (Fin d → Node ι) → Fin colors) :
    ∃ c : Fin colors,
      ∃ V : HomogeneousVectorStrongEmbedding ι d,
        ∀ (n : ℕ) (x : Fin d → Node ι),
          (∀ i, (x i).length = n) →
            colour (fun i => (V.coordinate i).toFun (x i)) = c := by
  obtain ⟨c, levels, F, hF, hc⟩ :=
    (HalpernLauchli.HalesJewettBridge.strongSubtreeHL ι)
      d colors colour
  exact ⟨c, ⟨F, levels, hF⟩, hc⟩

end Applications
end Milliken
