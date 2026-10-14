import Milliken.AmbientTree

/-!
# Strong subtrees of arbitrary finitely branching rooted ambient trees

This interface directly encodes the (str1)–(str2) definition of
Todorčević, *Introduction to Ramsey Spaces*, Chapter 6.
The branching degree may depend on both the node and its level and
may be unbounded across the whole ambient tree. Only the *individual*
successor sets of the ambient tree are required to be finite.

The unconditional arbitrary-ambient Milliken theorem is proved in
`GeneralTree.HeterogeneousUniversalMilliken`. This file isolates the
basic geometry; it does not itself import the combinatorial proof.

Source: Todorčević (2010), Chapter 6, (str1)–(str2), (6.1)–(6.2),
Theorem 6.2; and Milliken (1979).
-/

namespace Milliken
namespace GeneralTree

/-- An infinite strong subtree of an arbitrary pruned, finitely branching
rooted tree. The root may lie strictly above the ambient root.

At successive selected levels every *ambient* immediate-successor cone
contains exactly one node on the next selected level. This is the exact
strongness requirement of (str2), not merely an embedding or preservation
of meets. -/
structure StrongSubtree (U : AmbientTree) where
  carrier : Set U
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  root : U
  root_mem : root ∈ carrier
  root_level : U.level root = levels 0
  root_below : ∀ x ∈ carrier, root ≤ x
  carrier_levels : ∀ x ∈ carrier, ∃ n, U.level x = levels n
  /-- No ghost nodes: every node on a positive selected level lies above
  a node on the preceding selected level. This makes the induced
  source-level structure a genuine rooted subtree, rather than merely
  a set satisfying a one-way extension property. -/
  predecessor_exists :
    ∀ (n : ℕ) (z : U),
      z ∈ carrier → U.level z = levels (n + 1) →
        ∃ x : U,
          x ∈ carrier ∧ U.level x = levels n ∧ x ≤ z
  successor_unique :
    ∀ (n : ℕ) (x : U),
      x ∈ carrier → U.level x = levels n →
      ∀ (y : U), x ⋖ y →
        ∃! z : U,
          z ∈ carrier ∧ U.level z = levels (n + 1) ∧ y ≤ z

namespace StrongSubtree

variable {U : AmbientTree}

/-- The nodes on the `n`th selected *source* level. -/
def sourceLevel (S : StrongSubtree U) (n : ℕ) : Set U :=
  {x | x ∈ S.carrier ∧ U.level x = S.levels n}

/-- Each source level is nonempty: the ambient tree is pruned and
strongness supplies a successor above each ambient child. -/
theorem sourceLevel_nonempty (S : StrongSubtree U) (n : ℕ) :
    (S.sourceLevel n).Nonempty := by
  induction n with
  | zero =>
      exact ⟨S.root, S.root_mem, S.root_level⟩
  | succ n ih =>
      obtain ⟨x, hx, hlev⟩ := ih
      obtain ⟨y, hxy⟩ := U.has_child x
      obtain ⟨z, hz, _⟩ :=
        S.successor_unique n x hx hlev y hxy
      exact ⟨z, hz.1, hz.2.1⟩

/-- The first `n` selected source levels, regardless of gaps in ambient
heights. This is the carrier form of Todorčević's `r_n`. -/
def initialPart (S : StrongSubtree U) (n : ℕ) : Set U :=
  {x | x ∈ S.carrier ∧
    ∃ k : ℕ, k < n ∧ U.level x = S.levels k}

@[simp] theorem initialPart_zero (S : StrongSubtree U) :
    S.initialPart 0 = ∅ := by
  ext x
  simp [initialPart]

/-- Restriction to fewer source levels includes into the longer one. -/
theorem initialPart_mono (S : StrongSubtree U)
    {n m : ℕ} (hnm : n ≤ m) :
    S.initialPart n ⊆ S.initialPart m := by
  rintro x ⟨hx, k, hkn, hlevel⟩
  exact ⟨hx, k, lt_of_lt_of_le hkn hnm, hlevel⟩

/-- The initial part is contained in its infinite strong subtree. -/
theorem initialPart_subset (S : StrongSubtree U) (n : ℕ) :
    S.initialPart n ⊆ S.carrier := by
  intro x hx
  exact hx.1

/-- The natural refinement relation in the published theorem is simply
inclusion of the underlying subtrees. -/
def Refines (S T : StrongSubtree U) : Prop :=
  S.carrier ⊆ T.carrier

end StrongSubtree

/-- A finite strong approximation of height `n`, realised as the
first `n` source levels of an infinite strong subtree. This deliberately
does not assume a globally fixed branching degree. -/
structure FiniteApprox (U : AmbientTree) (n : ℕ) where
  carrier : Set U
  realised : ∃ S : StrongSubtree U, carrier = S.initialPart n

/-- Canonical approximation of an infinite strong subtree. -/
def approx {U : AmbientTree} (n : ℕ) (S : StrongSubtree U) :
    FiniteApprox U n :=
  ⟨S.initialPart n, ⟨S, rfl⟩⟩

/-- Exact original-style **statement** for arbitrary pruned finitely
branching ambient trees. It is a definition of the desired property,
NOT an axiom or a proved theorem.

For positive `n` this is the finite-colouring conclusion for *realised*
finite approximations; equivalence with all intrinsic finite strong
subtrees in Milliken (1979) is a separate extension obligation.
Allowing `n=0` adds the trivial empty case. The property is proved in
`HeterogeneousUniversalMilliken`. -/
def HasMillikenFiniteColourProperty (U : AmbientTree) : Prop :=
  ∀ (n colors : ℕ) [NeZero colors]
      (colour : FiniteApprox U n → Fin colors),
    ∃ S : StrongSubtree U,
      ∃ c : Fin colors,
        ∀ a : FiniteApprox U n,
          a.carrier ⊆ S.carrier → colour a = c

end GeneralTree
end Milliken
