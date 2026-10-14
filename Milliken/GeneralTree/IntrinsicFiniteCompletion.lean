import Milliken.GeneralTree.IntrinsicFinite

/-!
# Completion of intrinsic finite strong-tree patterns: level and cone geometry

An intrinsic finite strong subtree has `k` selected ambient levels but no
infinite realiser. To extend it, continue the selected levels by consecutive
ambient heights after the last finite level and include all complete
ambient descendant cones of the last frontier.

The lemmas in this file isolate the finite/infinite rank calculations and
the exact membership at or beyond the final frontier. The actual
`StrongSubtree` constructor and the reverse equivalence are separate
remaining proof steps; no unproved statement is assumed.
-/

namespace Milliken
namespace GeneralTree
namespace IntrinsicFiniteWitness

variable {U : AmbientTree} {n : ℕ}

/-- Extend a finite source-level sequence by consecutive ambient levels.
The finite part stays unchanged; from source level `n` onward, each
ambient height increases by exactly one. -/
def extendedLevels (W : IntrinsicFiniteWitness U (n + 1))
    (j : ℕ) : ℕ :=
  if h : j < n + 1 then
    W.levels ⟨j, h⟩
  else
    W.levels ⟨n, Nat.lt_succ_self n⟩ + (j - n)

/-- The first `n+1` extended levels are exactly the finite data. -/
@[simp] theorem extendedLevels_finite
    (W : IntrinsicFiniteWitness U (n + 1))
    (j : Fin (n + 1)) :
    W.extendedLevels j.1 = W.levels j := by
  simp [extendedLevels, j.isLt]

/-- From the last finite source level onward, the completion uses
successive ambient heights without skipping any level. -/
theorem extendedLevels_tail
    (W : IntrinsicFiniteWitness U (n + 1))
    (j : ℕ) (hj : n ≤ j) :
    W.extendedLevels j =
      W.levels ⟨n, Nat.lt_succ_self n⟩ + (j - n) := by
  by_cases h : j < n + 1
  · have heq : j = n := by omega
    subst j
    simp [extendedLevels]
  · simp [extendedLevels, h]

/-- Extended source levels are strictly increasing. All nontrivial
jumps lie in the given finite strong-tree witness. -/
theorem extendedLevels_strictMono
    (W : IntrinsicFiniteWitness U (n + 1)) :
    StrictMono W.extendedLevels := by
  apply strictMono_nat_of_lt_succ
  intro j
  by_cases hnext : j + 1 < n + 1
  · have hj : j < n + 1 := by omega
    calc
      W.extendedLevels j = W.levels ⟨j, hj⟩ :=
        W.extendedLevels_finite ⟨j, hj⟩
      _ < W.levels ⟨j + 1, hnext⟩ :=
        W.levels_strictMono (show (⟨j, hj⟩ : Fin (n + 1)) <
          ⟨j + 1, hnext⟩ by exact Nat.lt_succ_self j)
      _ = W.extendedLevels (j + 1) :=
        (W.extendedLevels_finite ⟨j + 1, hnext⟩).symm
  · have hj : n ≤ j := by omega
    rw [W.extendedLevels_tail j hj,
      W.extendedLevels_tail (j + 1) (by omega)]
    omega

/-- Keep all nodes of the intrinsic finite strong tree and attach all
ambient nodes descended from its last selected frontier. -/
def extensionCarrier (W : IntrinsicFiniteWitness U (n + 1)) :
    Set U :=
  W.carrier ∪ {z | ∃ x ∈ W.lastFrontier, x ≤ z}

/-- At or below the last selected finite height, completion adds
no new nodes. In particular the earlier finite source levels are
preserved exactly. -/
theorem mem_finite_of_extensionCarrier_of_level_le
    (W : IntrinsicFiniteWitness U (n + 1))
    {z : U} (hz : z ∈ W.extensionCarrier)
    (hlevel : U.level z ≤
      W.levels ⟨n, Nat.lt_succ_self n⟩) :
    z ∈ W.carrier := by
  rcases hz with hz | ⟨x, hx, hxz⟩
  · exact hz
  · change x ∈ W.carrier ∧
      U.level x = W.levels ⟨n, Nat.lt_succ_self n⟩ at hx
    have hle := U.level_mono hxz
    have hEqLevels : U.level x = U.level z := by omega
    have hEq : x = z :=
      U.eq_of_le_of_level_eq hxz hEqLevels
    simpa only [hEq] using hx.1

/-- Every completed node at or above the final finite level lies
in an actual complete descendant cone of the last frontier. -/
theorem extensionCarrier_has_last_ancestor
    (W : IntrinsicFiniteWitness U (n + 1))
    {z : U} (hz : z ∈ W.extensionCarrier)
    (hlevel :
      W.levels ⟨n, Nat.lt_succ_self n⟩ ≤ U.level z) :
    ∃ x ∈ W.lastFrontier, x ≤ z := by
  rcases hz with hz | htail
  · have hle := W.level_le_last hz
    have heq :
        U.level z = W.levels ⟨n, Nat.lt_succ_self n⟩ := by omega
    exact ⟨z, ⟨hz, heq⟩, le_rfl⟩
  · exact htail

/-- The intrinsic root remains below every completed node, whether
it is part of the original finite picture or a full descendant cone. -/
theorem root_below_extensionCarrier
    (W : IntrinsicFiniteWitness U (n + 1))
    {z : U} (hz : z ∈ W.extensionCarrier) :
    W.root ≤ z := by
  rcases hz with hz | ⟨x, hx, hxz⟩
  · exact W.root_below z hz
  · exact (W.root_below x hx.1).trans hxz

end IntrinsicFiniteWitness
end GeneralTree
end Milliken
