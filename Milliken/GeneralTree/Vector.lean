import Milliken.GeneralTree.Coherence

/-!
# Synchronized vector strong subtrees of arbitrary finitely branching trees

This is an abstract synchronized-vector interface for finite families of
strong trees. It can be used in applications to structural and big Ramsey
theory whenever a separate vector-tree colouring theorem is available.

Each coordinate tree is independently strong in its own rooted pruned
locally finite ambient tree. All coordinate trees share exactly ONE
strictly increasing sequence of selected ambient levels.

For now this module proves the basic restriction and refinement laws.
`HasVectorMillikenFiniteColourProperty` is a *definition of the target
theorem*, not a proof. The verified product Halpern–Läuchli theorem for
homogeneous trees is exposed separately in Applications/VectorHL.lean.
-/

namespace Milliken
namespace GeneralTree

/-- A vector of strong subtrees with ONE common selected level sequence.
The dimension is positive. With zero coordinates a stored level sequence
would be unobservable from all finite vector approximations, contradicting
A.1 separation. -/
structure StrongVectorSubtree {d : ℕ}
    (U : Fin d → AmbientTree) where
  coordinate : (i : Fin d) → StrongSubtree (U i)
  levels : ℕ → ℕ
  levels_strictMono : StrictMono levels
  synchronized : ∀ i, (coordinate i).levels = levels
  /-- A.1 separation requires at least one observable coordinate. -/
  dimension_pos : 0 < d

namespace StrongVectorSubtree

variable {d : ℕ} {U : Fin d → AmbientTree}

/-- Coordinatewise inclusion of vector strong subtrees. -/
def Refines (S T : StrongVectorSubtree U) : Prop :=
  ∀ i, (S.coordinate i).Refines (T.coordinate i)

theorem refines_refl (S : StrongVectorSubtree U) :
    S.Refines S := by
  intro i
  exact StrongSubtree.refines_refl _

theorem refines_trans {S T R : StrongVectorSubtree U}
    (hST : S.Refines T) (hTR : T.Refines R) :
    S.Refines R := by
  intro i
  exact StrongSubtree.refines_trans (hST i) (hTR i)

/-- Every coordinate uses the same selected ambient level set. -/
theorem coordinate_level (S : StrongVectorSubtree U)
    (i : Fin d) (n : ℕ) :
    (S.coordinate i).levels n = S.levels n := by
  rw [S.synchronized i]

/-- A vector strong subtree is determined by its coordinate strong trees:
when the index is nonempty, the common selected-level map is determined
by any one coordinate. -/
@[ext] theorem ext_coordinate {S T : StrongVectorSubtree U}
    (h : ∀ i, S.coordinate i = T.coordinate i) : S = T := by
  have hlevels : S.levels = T.levels := by
    let i : Fin d := ⟨0, S.dimension_pos⟩
    calc
      S.levels = (S.coordinate i).levels := (S.synchronized i).symm
      _ = (T.coordinate i).levels := by rw [h i]
      _ = T.levels := T.synchronized i
  have hcoord : S.coordinate = T.coordinate := funext h
  cases S
  cases T
  dsimp at hcoord hlevels
  cases hcoord
  cases hlevels
  rfl

end StrongVectorSubtree

/-- A realized finite synchronized vector strong subtree, with a
common source height n across all coordinates. The realized vectors'
selected ambient levels are also synchronized. -/
structure FiniteVectorApprox {d : ℕ}
    (U : Fin d → AmbientTree) (n : ℕ) where
  carriers : (i : Fin d) → Set (U i)
  realised :
    ∃ S : StrongVectorSubtree U,
      ∀ i, carriers i = (S.coordinate i).initialPart n

/-- Restrict every coordinate to the same first n *source* levels. -/
def vectorApprox {d : ℕ} {U : Fin d → AmbientTree}
    (n : ℕ) (S : StrongVectorSubtree U) :
    FiniteVectorApprox U n :=
  ⟨(fun i => (S.coordinate i).initialPart n),
    ⟨S, fun _ => rfl⟩⟩

namespace FiniteVectorApprox

variable {d : ℕ} {U : Fin d → AmbientTree} {n : ℕ}

/-- Realisation proofs carry no extra data: a vector approximation is
determined by its coordinate carriers. -/
theorem ext_carriers {a b : FiniteVectorApprox U n}
    (h : ∀ i, a.carriers i = b.carriers i) : a = b := by
  cases a with
  | mk ca ha =>
    cases b with
    | mk cb hb =>
      have hc : ca = cb := by
        funext i
        exact h i
      cases hc
      rfl

end FiniteVectorApprox

/-- Every realized vector approximation comes from an infinite vector
strong subtree, just as in A.1. -/
theorem vectorApprox_surjective {d : ℕ}
    {U : Fin d → AmbientTree} (n : ℕ) :
    Function.Surjective (vectorApprox (U := U) n) := by
  intro a
  obtain ⟨S, hS⟩ := a.realised
  refine ⟨S, ?_⟩
  apply FiniteVectorApprox.ext_carriers
  intro i
  exact (hS i).symm

/-- The height-zero vector approximation is independent of the tree. -/
theorem vectorApprox_zero_eq {d : ℕ}
    {U : Fin d → AmbientTree} (S T : StrongVectorSubtree U) :
    vectorApprox 0 S = vectorApprox 0 T := by
  apply FiniteVectorApprox.ext_carriers
  intro i
  simp only [vectorApprox, StrongSubtree.initialPart_zero]

/-- A.1 separation for synchronized vector strong trees. The positive
vector dimension excludes invisible level maps when there are no
coordinates. -/
theorem vectorApprox_separated {d : ℕ} {U : Fin d → AmbientTree}
    {S T : StrongVectorSubtree U}
    (h : ∀ n : ℕ, vectorApprox n S = vectorApprox n T) : S = T := by
  apply StrongVectorSubtree.ext_coordinate
  intro i
  apply r_separated
  intro n
  apply FiniteApprox.ext_carrier
  exact congrArg
    (fun a : FiniteVectorApprox U n => a.carriers i) (h n)

/-- A.1 coherence for synchronized vector approximations: equality of
finite height-n pictures implies equality of all lower restrictions. -/
theorem vectorApprox_coherent {d : ℕ} {U : Fin d → AmbientTree}
    {S T : StrongVectorSubtree U} {n m : ℕ}
    (h : vectorApprox n S = vectorApprox n T)
    (hm : m ≤ n) :
    vectorApprox m S = vectorApprox m T := by
  apply FiniteVectorApprox.ext_carriers
  intro i
  have hi : r n (S.coordinate i) = r n (T.coordinate i) := by
    apply FiniteApprox.ext_carrier
    exact congrArg
      (fun a : FiniteVectorApprox U n => a.carriers i) h
  have him := r_coherent_le (S.coordinate i) (T.coordinate i)
    n hi m hm
  exact congrArg FiniteApprox.carrier him

/-- Basic vector Ellentuck neighbourhood with a fixed finite vector stem. -/
def VectorBasicNeighborhood {d : ℕ}
    {U : Fin d → AmbientTree} {n : ℕ}
    (a : FiniteVectorApprox U n)
    (T : StrongVectorSubtree U) :
    Set (StrongVectorSubtree U) :=
  {S | S.Refines T ∧ vectorApprox n S = a}

theorem self_mem_vectorBasicNeighborhood {d : ℕ}
    {U : Fin d → AmbientTree}
    (T : StrongVectorSubtree U) (n : ℕ) :
    T ∈ VectorBasicNeighborhood (vectorApprox n T) T := by
  exact ⟨StrongVectorSubtree.refines_refl T, rfl⟩

/-- The synchronized vector finite-colour conclusion.
This is currently an *unproved property* for arbitrary ambients, not an
axiom or a theorem. The finite-vector-tree theorem is stronger than
monochromatic level products supplied by Halpern–Läuchli. -/
def HasVectorMillikenFiniteColourProperty {d : ℕ}
    (U : Fin d → AmbientTree) : Prop :=
  ∀ (n colors : ℕ) [NeZero colors]
      (colour : FiniteVectorApprox U n → Fin colors),
    ∃ S : StrongVectorSubtree U,
      ∃ c : Fin colors,
        ∀ a : FiniteVectorApprox U n,
          (∀ i, a.carriers i ⊆ (S.coordinate i).carrier) →
            colour a = c

/-- Fixed-stem vector colouring, formulated on infinite refinements
without needing an as-yet-unproved intrinsic finite-vector restriction
lemma.  This is a *property*, not an assumed or proved theorem. -/
def HasVectorFixedStemColourProperty {d : ℕ}
    (U : Fin d → AmbientTree) : Prop :=
  ∀ (ell k colors : ℕ) [NeZero colors]
      (A : StrongVectorSubtree U)
      (colour : FiniteVectorApprox U k → Fin colors),
    ∃ B : StrongVectorSubtree U,
      B.Refines A ∧ vectorApprox ell B = vectorApprox ell A ∧
        ∃ c : Fin colors,
          ∀ X : StrongVectorSubtree U,
            X.Refines B →
            vectorApprox ell X = vectorApprox ell A →
              colour (vectorApprox k X) = c

end GeneralTree
end Milliken
