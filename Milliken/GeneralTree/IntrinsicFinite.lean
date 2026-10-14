import Milliken.GeneralTree.FiniteLevels

/-!
# Intrinsic finite strong subtrees of arbitrary locally finite trees

Todorčević `S_k(U)` and Milliken's 1979 paper quantify over finite
strong subtrees *without* a preselected infinite realisation.
The original `FiniteApprox U k` in this library instead stores the
proposition that the finite carrier is `r k S` for an infinite S.

This file begins the comparison using a genuine finite witness:
only the k selected level indices and the internal k-1 successor
steps are given. There is NO infinite strong subtree in the
definition. This distinction matters for source-faithful finite
colourings.

The forward map from realised approximations to intrinsic finite
strong trees is straightforward. The converse is a substantive
completion theorem: above the last selected level, extend all
terminal cones using the pruned ambient. It must be proved separately.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- Finite combinatorial witness for a strong subtree of source height `k`.

For `k=0`, the carrier is empty. When `k>0`, the root is retained.
All levels are recorded by the *finite* index type `Fin k`.
Successor uniqueness is required only at the `k-1` internal steps.
The predecessor condition prevents ghost nodes on any later finite
source level. No infinite realiser appears here. -/
structure IntrinsicFiniteWitness (U : AmbientTree) (k : ℕ) where
  carrier : Set U
  carrier_finite : carrier.Finite
  levels : Fin k → ℕ
  levels_strictMono : StrictMono levels
  root : U
  root_mem : 0 < k → root ∈ carrier
  root_level : ∀ (h : 0 < k), U.level root = levels ⟨0, h⟩
  root_below : ∀ x ∈ carrier, root ≤ x
  carrier_levels : ∀ x ∈ carrier, ∃ j : Fin k, U.level x = levels j
  predecessor_exists :
    ∀ (j : ℕ) (hj : j + 1 < k) (z : U),
      z ∈ carrier →
        U.level z = levels ⟨j + 1, hj⟩ →
        ∃ x : U,
          x ∈ carrier ∧
          U.level x = levels ⟨j, by omega⟩ ∧ x ≤ z
  successor_unique :
    ∀ (j : ℕ) (hj : j + 1 < k) (x : U),
      x ∈ carrier →
        U.level x = levels ⟨j, by omega⟩ →
        ∀ (y : U), x ⋖ y →
          ∃! z : U,
            z ∈ carrier ∧
              U.level z = levels ⟨j + 1, hj⟩ ∧ y ≤ z
  empty_of_zero : k = 0 → carrier = ∅

/-- Intrinsic finite strong subtree, up to equality of its node
carrier. Different choices of proof/witness do not give different
finite colouring objects. In particular, no infinite realisation
is part of its definition. -/
structure IntrinsicFiniteApprox (U : AmbientTree) (k : ℕ) where
  carrier : Set U
  intrinsic : ∃ W : IntrinsicFiniteWitness U k, W.carrier = carrier

namespace IntrinsicFiniteApprox

@[ext] theorem ext_carrier
    {a b : IntrinsicFiniteApprox U k}
    (h : a.carrier = b.carrier) : a = b := by
  cases a with
  | mk A hA =>
    cases b with
    | mk B hB =>
      cases h
      rfl

theorem carrier_finite (a : IntrinsicFiniteApprox U k) :
    a.carrier.Finite := by
  obtain ⟨W, hW⟩ := a.intrinsic
  rw [← hW]
  exact W.carrier_finite

end IntrinsicFiniteApprox

/-- The actual first `k` source levels of any infinite strong tree
form an intrinsically finite strong subtree. Only finite geometry
is used; no completion argument is required in this direction. -/
def intrinsicWitnessOfStrong (S : StrongSubtree U) (k : ℕ) :
    IntrinsicFiniteWitness U k where
  carrier := S.initialPart k
  carrier_finite := S.initialPart_finite k
  levels := fun i => S.levels i
  levels_strictMono := by
    intro i j hij
    exact S.levels_strictMono (Fin.lt_iff_val_lt_val.mp hij)
  root := S.root
  root_mem := by
    intro hk
    exact ⟨S.root_mem, 0, hk, S.root_level⟩
  root_level := by
    intro hk
    exact S.root_level
  root_below := by
    intro x hx
    exact S.root_below x hx.1
  carrier_levels := by
    intro x hx
    obtain ⟨_, j, hj, hlev⟩ := hx
    exact ⟨⟨j, hj⟩, hlev⟩
  predecessor_exists := by
    intro j hj z hz hlev
    obtain ⟨x, hx, hl, hxz⟩ :=
      S.predecessor_exists j z hz.1 hlev
    exact ⟨x, ⟨hx, j, by omega, hl⟩, hl, hxz⟩
  successor_unique := by
    intro j hj x hx hlev y hxy
    obtain ⟨z, hz, hUnique⟩ :=
      S.successor_unique j x hx.1 hlev y hxy
    refine ⟨z, ⟨⟨hz.1, j + 1, hj, hz.2.1⟩,
      hz.2.1, hz.2.2⟩, ?_⟩
    intro w hw
    exact hUnique w ⟨hw.1.1, hw.2.1, hw.2.2⟩
  empty_of_zero := by
    intro hk
    subst k
    exact S.initialPart_zero

/-- Every *realised* finite approximation is intrinsic. The reverse
direction is intentionally not assumed: it needs the finite-to-infinite
extension theorem. -/
noncomputable def FiniteApprox.toIntrinsic
    {k : ℕ} (a : FiniteApprox U k) :
    IntrinsicFiniteApprox U k := by
  classical
  let S : StrongSubtree U := Classical.choose a.realised
  have ha : a.carrier = S.initialPart k :=
    Classical.choose_spec a.realised
  exact ⟨a.carrier, ⟨intrinsicWitnessOfStrong S k, ha.symm⟩⟩

@[simp] theorem FiniteApprox.toIntrinsic_carrier
    {k : ℕ} (a : FiniteApprox U k) :
    a.toIntrinsic.carrier = a.carrier := rfl

/-- The intrinsic representation agrees on carriers with truncation
of any infinite strong subtree. -/
@[simp] theorem toIntrinsic_r_carrier (S : StrongSubtree U) (k : ℕ) :
    ((r k S).toIntrinsic).carrier = S.initialPart k := rfl

end GeneralTree
end Milliken
