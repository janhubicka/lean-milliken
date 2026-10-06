import Milliken.Graft
import Milliken.RamseyBasic

/-!
# Boundary grafts in the strong-tree Ramsey space

The source-side boundary graft fixes every node strictly below the boundary
height.  Therefore it fixes the corresponding finite approximation.  After
composition with an ambient strong embedding `T`, the graft is a reduction
of `T` lying in the level neighborhood `[n,T]`.

These are the formal counterparts of the repeated assertion
`S ∈ [n,T]` in Todorčević's proof of Lemma 6.1.
-/

namespace Milliken
namespace BoundaryGraft

universe u

variable {ι : Type u} {n : ℕ}

/-- A boundary graft has the identity `n`th approximation. -/
theorem approx_graft_eq_id [Nonempty ι]
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrongTreeSpace.approx ι n (graft F hF) =
      StrongTreeSpace.approx ι n StrongEmbedding.id := by
  apply Subtype.ext
  funext s
  change (graft F hF).toFun s.1 = s.1
  exact graft_toFun_of_lt F hF s.1 s.2

/-- Grafting below an ambient tree preserves its first `n` levels. -/
theorem approx_comp_graft [Nonempty ι]
    (T : StrongEmbedding ι)
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrongTreeSpace.approx ι n
        (StrongEmbedding.comp T (graft F hF)) =
      StrongTreeSpace.approx ι n T := by
  apply Subtype.ext
  funext s
  change T.toFun ((graft F hF).toFun s.1) = T.toFun s.1
  rw [graft_toFun_of_lt F hF s.1 s.2]

/-- The composed graft is a reduction of the ambient strong tree. -/
theorem comp_graft_le [Nonempty ι]
    (T : StrongEmbedding ι)
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrongTreeSpace.le ι (StrongEmbedding.comp T (graft F hF)) T :=
  ⟨graft F hF, rfl⟩

/-- In Ramsey-space language, a composed boundary graft belongs to
`[n,T]`. -/
theorem comp_graft_mem_levelNeighborhood [Nonempty ι]
    (T : StrongEmbedding ι)
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : HasCommonLevels F) :
    StrongEmbedding.comp T (graft F hF) ∈
      (StrongTreeSpace.approximationSystem ι).levelNeighborhood n T := by
  constructor
  · exact comp_graft_le T F hF
  · exact approx_comp_graft T F hF

end BoundaryGraft
end Milliken
