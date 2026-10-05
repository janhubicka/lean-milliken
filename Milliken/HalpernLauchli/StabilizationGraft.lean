import Milliken.Graft
import Milliken.HalpernLauchli.LevelSelector

/-!
# Explicit common levels for boundary grafts

Boundary grafting already proves that each graft is a strong embedding.  In
the Chapter 3 fusion we graft several coordinates independently, so we also
need to know that all resulting coordinate embeddings use exactly the same
level map whenever all attached boundary embeddings use the same relative
level map.  The formula is elementary and is recorded here once.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Absolute level map of a graft at source height `n` whose attached
embeddings use the relative level map `levels`. -/
def graftLevelMap (n : ℕ) (levels : ℕ → ℕ) (k : ℕ) : ℕ :=
  if k < n then k else n + levels (k - n)

theorem graftLevelMap_strictMono
    (n : ℕ) {levels : ℕ → ℕ}
    (hlevels : StrictMono levels) :
    StrictMono (graftLevelMap n levels) := by
  intro a b hab
  by_cases hb : b < n
  · have ha : a < n := hab.trans hb
    simp [graftLevelMap, ha, hb, hab]
  · have hbn : n ≤ b := le_of_not_gt hb
    by_cases ha : a < n
    · simp [graftLevelMap, ha, hb]
      have hnonneg : 0 ≤ levels (b - n) := Nat.zero_le _
      omega
    · have han : n ≤ a := le_of_not_gt ha
      have hsub : a - n < b - n := by omega
      simp [graftLevelMap, ha, hb]
      exact Nat.add_lt_add_left (hlevels hsub) n

/-- Length formula for one boundary graft when the common relative levels
are supplied explicitly. -/
theorem boundaryGraft_length
    [Nonempty ι]
    {n : ℕ}
    (F : LevelNode ι n → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hF :
      ∀ b s, ((F b).toFun s).length = levels s.length)
    (s : Node ι) :
    ((BoundaryGraft.graft F
      ⟨levels, hlevels, hF⟩).toFun s).length =
      graftLevelMap n levels s.length := by
  by_cases hs : s.length < n
  · rw [BoundaryGraft.graft_toFun_of_lt
      F ⟨levels, hlevels, hF⟩ s hs]
    simp [graftLevelMap, hs]
  · have hsge : n ≤ s.length := le_of_not_gt hs
    change (BoundaryGraft.graftFun F s).length =
      graftLevelMap n levels s.length
    rw [BoundaryGraft.graftFun_of_ge F s hsge,
      List.length_append,
      (BoundaryGraft.boundaryPrefix n s hsge).2,
      hF]
    simp [graftLevelMap, hs]

/-- Coordinatewise boundary grafts have one common absolute level map when
all boundary families have one common relative level map. -/
theorem boundaryGrafts_commonLevels
    [Nonempty ι]
    {d n : ℕ}
    (F : Fin d → LevelNode ι n → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hF :
      ∀ i b s, ((F i b).toFun s).length = levels s.length) :
    HasCommonLevels
      (fun i =>
        BoundaryGraft.graft (F i)
          ⟨levels, hlevels, fun b s => hF i b s⟩)
      (graftLevelMap n levels) := by
  refine ⟨graftLevelMap_strictMono n hlevels, ?_⟩
  intro i s
  exact boundaryGraft_length
    (F i) levels hlevels (fun b t => hF i b t) s

end HalpernLauchli
end Milliken
