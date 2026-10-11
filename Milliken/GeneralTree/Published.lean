import Milliken.GeneralTree

/-!
# Todorčević §6.1: source-faithful tree-space notation and orders

For an arbitrary pruned finitely branching rooted ambient tree `U`,
`SInfinity U` and `SFinite U n` denote its infinite strong subtrees and
height-`n` finite approximations. We expose the literal objects and
relations from (6.1)–(6.3):

* `r n T` is the first `n` **selected source** levels of `T`;
* `BasicNeighborhood a T` is the set of strong refinements of `T`
  with first `n` levels `a`;
* `maxLevel a` consists of the maximal nodes in the induced finite
  subtree, which agrees with its last selected source level;
* `bookLeFin` uses carrier inclusion and inclusion of maximal levels,
  including the convention for two empty approximations.

These are definitions and elementary checked lemmas, not a proof of
Todorčević's general Theorem 6.2. That proof is still required to
construct the Ramsey-space instance for all `U`.
-/

namespace Milliken
namespace GeneralTree

/-- Published `S_∞(U)`: infinite strong subtrees of `U`. -/
abbrev SInfinity (U : AmbientTree) := StrongSubtree U

/-- Published `S_n(U)`: finite strong approximations of height `n`. -/
abbrev SFinite (U : AmbientTree) (n : ℕ) := FiniteApprox U n

/-- Published `r_n(T) = T ↾ n`, see (6.1). -/
def r {U : AmbientTree} (n : ℕ) (T : SInfinity U) : SFinite U n :=
  approx n T

/-- Published `[a,T]` basic neighbourhood of strong subtrees with
initial approximation `a`, where `a` has height `n`. -/
def BasicNeighborhood {U : AmbientTree} {n : ℕ}
    (a : SFinite U n) (T : SInfinity U) : Set (SInfinity U) :=
  {S | S.Refines T ∧ r n S = a}

/-- Every tree is in its own basic neighbourhood for any selected height. -/
theorem self_mem_basicNeighborhood {U : AmbientTree}
    (T : SInfinity U) (n : ℕ) :
    T ∈ BasicNeighborhood (r n T) T := by
  exact ⟨fun _ h => h, rfl⟩

/-- The maximal level `a(max)` in (6.3), defined from the induced
tree order rather than choosing a realizer or a selected level. -/
def maxLevel {U : AmbientTree} {n : ℕ}
    (a : SFinite U n) : Set U :=
  {x | x ∈ a.carrier ∧
    ∀ y ∈ a.carrier, x ≤ y → y = x}

/-- Every maximal node of an approximation belongs to its carrier. -/
theorem maxLevel_subset_carrier {U : AmbientTree} {n : ℕ}
    (a : SFinite U n) :
    maxLevel a ⊆ a.carrier :=
  fun _ h => h.1

/-- Todorčević's literal finite order (6.3):
`a = b = ∅` or `a ⊆ b` and `a(max) ⊆ b(max)`.
The two-empty case is retained explicitly as in the printed statement. -/
def bookLeFin {U : AmbientTree}
    (a b : Σ n, SFinite U n) : Prop :=
  (a.2.carrier = ∅ ∧ b.2.carrier = ∅) ∨
    (a.2.carrier ⊆ b.2.carrier ∧
      maxLevel a.2 ⊆ maxLevel b.2)

/-- The (6.3) order is reflexive. -/
theorem bookLeFin_refl {U : AmbientTree}
    (a : Σ n, SFinite U n) :
    bookLeFin a a :=
  Or.inr ⟨fun _ h => h, fun _ h => h⟩

/-- The empty selected initial part really has empty carrier. -/
@[simp] theorem r_zero_carrier {U : AmbientTree}
    (T : SInfinity U) :
    (r 0 T).carrier = ∅ :=
  StrongSubtree.initialPart_zero T

/-- The empty approximation is below *every* finite approximation in
the literal (6.3) relation. -/
theorem bookLeFin_zero_left {U : AmbientTree}
    (T : SInfinity U) (b : Σ n, SFinite U n) :
    bookLeFin ⟨0, r 0 T⟩ b := by
  right
  constructor
  · intro x hx
    have hempty : (r 0 T).carrier = ∅ := r_zero_carrier T
    rw [hempty] at hx
    exact False.elim (Set.not_mem_empty x hx)
  · intro x hx
    have he : x ∈ (r 0 T).carrier :=
      maxLevel_subset_carrier (r 0 T) hx
    have hempty : (r 0 T).carrier = ∅ := r_zero_carrier T
    rw [hempty] at he
    exact False.elim (Set.not_mem_empty x he)

end GeneralTree
end Milliken
