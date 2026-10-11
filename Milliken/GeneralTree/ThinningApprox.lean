import Milliken.GeneralTree.ThinningPrefix
import Milliken.GeneralTree.ThinningStrong

/-!
# Approximation preservation by source-level thinning

When a strictly increasing source-index map is the identity through
source level j, the genuine recursively thinned strong subtree has
exactly B's first j+1 selected source levels, hence exactly the same
height-(j+1) finite strong approximation.

This is the prefix-preservation endpoint needed when constructing
the depth-d background D for Todorčević A.3(2).
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Every thinned source level up to j is the full original
selected B-source level, provided f fixes the initial indices. -/
theorem thinStrong_sourceLevel_of_fixed
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (j : ℕ)
    (hfixed : ∀ k : ℕ, k ≤ j → f k = k)
    {k : ℕ} (hk : k ≤ j) :
    (B.thinStrong f hf hf0).sourceLevel k =
      B.sourceLevel k := by
  rw [B.thinStrong_sourceLevel f hf hf0 k]
  exact B.thinningLevel_full_prefix f hf hf0 k
    (fun l hl => hfixed l (hl.trans hk))

/-- Fixing all source indices up to j preserves the entire
height-(j+1) finite selected strong tree. -/
theorem thinStrong_approx_succ_of_fixed
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (j : ℕ)
    (hfixed : ∀ k : ℕ, k ≤ j → f k = k) :
    r (j + 1) (B.thinStrong f hf hf0) = r (j + 1) B := by
  let T := B.thinStrong f hf hf0
  apply FiniteApprox.ext_carrier
  change T.initialPart (j + 1) = B.initialPart (j + 1)
  ext z
  constructor
  · rintro ⟨hz, k, hkj, hzLevel⟩
    have hk : k ≤ j := Nat.le_of_lt_succ hkj
    have hzT : z ∈ T.sourceLevel k := ⟨hz, hzLevel⟩
    have hsource : T.sourceLevel k = B.sourceLevel k :=
      B.thinStrong_sourceLevel_of_fixed f hf hf0 j
        hfixed hk
    rw [hsource] at hzT
    exact ⟨hzT.1, k, hkj, hzT.2⟩
  · rintro ⟨hz, k, hkj, hzLevel⟩
    have hk : k ≤ j := Nat.le_of_lt_succ hkj
    have hzB : z ∈ B.sourceLevel k := ⟨hz, hzLevel⟩
    have hsource : T.sourceLevel k = B.sourceLevel k :=
      B.thinStrong_sourceLevel_of_fixed f hf hf0 j
        hfixed hk
    rw [← hsource] at hzB
    exact ⟨hzB.1, k, hkj, hzB.2⟩

end StrongSubtree
end GeneralTree
end Milliken
