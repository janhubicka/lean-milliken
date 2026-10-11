import Milliken.GeneralTree.SpliceCones

/-!
# Strong successor cones inside arbitrary finitely branching rooted trees

For a strong subtree T and any node x on its selected source level n,
the set of retained descendants of x forms another genuine infinite
strong subtree of the *same ambient tree* U. Its root is x and its
selected ambient levels are k ↦ T.levels (n+k).

This exposes the actual factors to which a general heterogeneous-cone
Halpern–Läuchli theorem must be applied in the proof of A.4. No global
branching-degree bound is introduced. No HL theorem is assumed here.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- The strong successor cone of a retained node x in T.
The strongness conditions remain relative to all *ambient*
immediate-successor cones of U. -/
noncomputable def coneStrong
    (T : StrongSubtree U) (n : ℕ) (x : U)
    (hx : x ∈ T.sourceLevel n) : StrongSubtree U where
  carrier := {z : U | z ∈ T.carrier ∧ x ≤ z}
  levels := fun k => T.levels (n + k)
  levels_strictMono := by
    intro a b hab
    exact T.levels_strictMono (by omega)
  root := x
  root_mem := ⟨hx.1, le_rfl⟩
  root_level := by
    change U.level x = T.levels (n + 0)
    simpa only [Nat.add_zero] using hx.2
  root_below := by
    intro z hz
    exact hz.2
  carrier_levels := by
    intro z hz
    obtain ⟨m, hm⟩ := T.carrier_levels z hz.1
    have hnm : n ≤ m := by
      have hle : T.levels n ≤ T.levels m := by
        calc
          T.levels n = U.level x := hx.2.symm
          _ ≤ U.level z := U.level_mono hz.2
          _ = T.levels m := hm
      by_contra hnot
      have hlt := T.levels_strictMono (Nat.lt_of_not_ge hnot)
      omega
    refine ⟨m - n, ?_⟩
    have hindex : n + (m - n) = m := by omega
    simpa only [hindex] using hm
  predecessor_exists := by
    intro k z hz hzlevel
    have hlevelT : U.level z = T.levels ((n + k) + 1) := by
      have hidx : n + (k + 1) = (n + k) + 1 := by omega
      simpa only [hidx] using hzlevel
    obtain ⟨p, hp, hpl, hpz⟩ :=
      T.predecessor_exists (n + k) z hz.1 hlevelT
    have hrootp : x ≤ p := by
      apply U.le_of_common_descendant_of_level_le hz.2 hpz
      calc
        U.level x = T.levels n := hx.2
        _ ≤ T.levels (n + k) :=
          T.levels_strictMono.monotone (by omega)
        _ = U.level p := hpl.symm
    exact ⟨p, ⟨hp, hrootp⟩, hpl, hpz⟩
  successor_unique := by
    intro k z hz hzlevel y hzy
    have hlevelT : U.level z = T.levels (n + k) := hzlevel
    obtain ⟨w, hw, huniq⟩ :=
      T.successor_unique (n + k) z hz.1 hlevelT y hzy
    refine ⟨w, ⟨⟨hw.1, ?_⟩, ?_, hw.2.2⟩, ?_⟩
    · exact hz.2.trans (hzy.le.trans hw.2.2)
    · have hidx : n + (k + 1) = (n + k) + 1 := by omega
      simpa only [hidx] using hw.2.1
    · intro v hv
      have hvT :
          v ∈ T.carrier ∧
            U.level v = T.levels ((n + k) + 1) ∧
            y ≤ v := by
        refine ⟨hv.1.1, ?_, hv.2.2⟩
        have hidx : n + (k + 1) = (n + k) + 1 := by omega
        simpa only [hidx] using hv.2.1
      exact huniq v hvT

/-- The successor cone is a refinement of its containing strong tree. -/
theorem coneStrong_refines
    (T : StrongSubtree U) (n : ℕ) (x : U)
    (hx : x ∈ T.sourceLevel n) :
    (T.coneStrong n x hx).Refines T :=
  fun _ hz => hz.1

/-- Its kth source level consists exactly of the T-nodes
on source level n+k descending from x. -/
theorem coneStrong_sourceLevel
    (T : StrongSubtree U) (n : ℕ) (x : U)
    (hx : x ∈ T.sourceLevel n) (k : ℕ) :
    (T.coneStrong n x hx).sourceLevel k =
      {z : U | z ∈ T.sourceLevel (n + k) ∧ x ≤ z} := by
  ext z
  constructor
  · rintro ⟨⟨hzT, hxz⟩, hlev⟩
    exact ⟨⟨hzT, hlev⟩, hxz⟩
  · rintro ⟨⟨hzT, hlev⟩, hxz⟩
    exact ⟨⟨hzT, hxz⟩, hlev⟩

/-- The cone has x as its actual root. -/
@[simp] theorem coneStrong_root
    (T : StrongSubtree U) (n : ℕ) (x : U)
    (hx : x ∈ T.sourceLevel n) :
    (T.coneStrong n x hx).root = x := rfl

end StrongSubtree
end GeneralTree
end Milliken
