import Milliken.HalpernLauchli.StabilizationPair

/-!
# Pulling sections through front-coordinate refinements

The stabilization fusion only thins the first `d` coordinates; the last tree
is left unchanged.  This file packages the corresponding pullback operation,
its interaction with sections, and the elementary composition laws needed to
iterate local boundary refinements.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Pull a `(d+1)`-dimensional set back through embeddings in its first
`d` coordinates, leaving the last coordinate unchanged. -/
def pullbackFront {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (F : Fin d → StrongEmbedding ι) :
    Set (Fin (d + 1) → Node ι) :=
  {z |
    appendLast (mapTuple F (front z)) (last z) ∈ P}

/-- Sections of the front pullback are exactly pullbacks of the original
sections. -/
theorem mem_lastSection_pullbackFront
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (F : Fin d → StrongEmbedding ι)
    (y : Node ι)
    (x : Fin d → Node ι) :
    x ∈ lastSection (pullbackFront P F) y ↔
      x ∈ pullbackProduct F (lastSection P y) := by
  simp [lastSection, pullbackFront, pullbackProduct,
    mapTuple, front_appendLast, last_appendLast]

/-- Coordinatewise composition of two embedding families. -/
def compFamily {d : ℕ}
    (F G : Fin d → StrongEmbedding ι) :
    Fin d → StrongEmbedding ι :=
  fun i => StrongEmbedding.comp (F i) (G i)

@[simp] theorem mapTuple_compFamily
    {d : ℕ}
    (F G : Fin d → StrongEmbedding ι)
    (x : Fin d → Node ι) :
    mapTuple (compFamily F G) x =
      mapTuple F (mapTuple G x) := by
  rfl

theorem pullbackProduct_comp
    {d : ℕ}
    (F G : Fin d → StrongEmbedding ι)
    (A : Set (Fin d → Node ι)) :
    pullbackProduct G (pullbackProduct F A) =
      pullbackProduct (compFamily F G) A := by
  ext x
  rfl

theorem pullbackFront_comp
    {d : ℕ}
    (P : Set (Fin (d + 1) → Node ι))
    (F G : Fin d → StrongEmbedding ι) :
    pullbackFront (pullbackFront P F) G =
      pullbackFront P (compFamily F G) := by
  ext z
  simp [pullbackFront, mapTuple, compFamily,
    front_appendLast, last_appendLast]

theorem compFamily_commonLevels
    {d : ℕ}
    {F G : Fin d → StrongEmbedding ι}
    {f g : ℕ → ℕ}
    (hF : HasCommonLevels F f)
    (hG : HasCommonLevels G g) :
    HasCommonLevels (compFamily F G)
      (fun n => f (g n)) := by
  exact hF.comp hG

theorem compFamily_fixesBelow
    {d n : ℕ}
    {F G : Fin d → StrongEmbedding ι}
    (hF : FixesBelow n F)
    (hG : FixesBelow n G) :
    FixesBelow n (compFamily F G) := by
  intro i s hs
  change (F i).toFun ((G i).toFun s) = s
  rw [hG i s hs]
  exact hF i s hs

theorem compFamily_preservesBoundary
    {d n : ℕ}
    {F G : Fin d → StrongEmbedding ι}
    (hF : PreservesBoundary n F)
    (hG : PreservesBoundary n G) :
    PreservesBoundary n (compFamily F G) := by
  intro i s hs
  have htakeG :
      ((G i).toFun s).take n = s.take n :=
    hG i s hs
  have htakeLen :
      (((G i).toFun s).take n).length = n := by
    rw [htakeG, List.length_take_of_le hs]
  have hnG : n ≤ ((G i).toFun s).length := by
    have hp :=
      (List.take_prefix n ((G i).toFun s)).length_le
    rw [htakeLen] at hp
    exact hp
  change
    ((F i).toFun ((G i).toFun s)).take n =
      s.take n
  rw [hF i ((G i).toFun s) hnG, htakeG]

/-- Previously established cone constancy survives composition with another
boundary-preserving common-level refinement. -/
theorem constantAbove_pullback_comp
    [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    {A : Set (Fin d → Node ι)}
    {x : LevelVector ι d n}
    {F : Fin d → StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hconst : ConstantAbove A x)
    (hF : HasCommonLevels F levels)
    (hboundary : PreservesBoundary n F) :
    ConstantAbove (pullbackProduct F A) x :=
  constantAbove_pullback hd hconst hF hboundary

end HalpernLauchli
end Milliken
