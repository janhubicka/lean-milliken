import Milliken.RamseyBasic
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Finite.Range

/-!
# Finite strong-tree approximations

This file isolates the finite carriers used in Todorčević's finitization
(6.3).  An approximation is already represented by the restriction of a
strong embedding to source nodes below a fixed height.  Its carrier is the
finite set of image nodes, and its maximal level is the image of source nodes
on the last source level.

The explicit height inequality in `leFin` is redundant for realized strong
subtrees, but is retained in the Lean relation because it makes finiteness of
lower cones transparent.  It will be proved equivalent to the book's
carrier/maximal-level formulation.
-/

namespace Milliken
namespace StrongTreeSpace

universe u
variable {ι : Type u}

/-- Nodes occurring in a finite approximation. -/
def approxCarrier {n : ℕ} (a : Approx ι n) : Set (Node ι) :=
  Set.range a.1

/-- The maximal level of a nonempty finite approximation.  For height zero
this is empty automatically because there is no source node satisfying the
displayed equation. -/
def approxMaxLevel {n : ℕ} (a : Approx ι n) : Set (Node ι) :=
  {x | ∃ s : FiniteNode ι n, s.1.length + 1 = n ∧ a.1 s = x}

theorem approxMaxLevel_subset_carrier {n : ℕ} (a : Approx ι n) :
    approxMaxLevel a ⊆ approxCarrier a := by
  rintro x ⟨s, hs, rfl⟩
  exact ⟨s, rfl⟩

theorem finite_finiteNode [Finite ι] (n : ℕ) :
    Finite (FiniteNode ι n) :=
  (List.finite_length_lt ι n).to_subtype

theorem approxCarrier_finite [Finite ι] {n : ℕ} (a : Approx ι n) :
    (approxCarrier a).Finite := by
  letI : Finite (FiniteNode ι n) := finite_finiteNode (ι := ι) n
  exact Set.finite_range _

theorem approxMaxLevel_finite [Finite ι] {n : ℕ} (a : Approx ι n) :
    (approxMaxLevel a).Finite :=
  (approxCarrier_finite a).subset (approxMaxLevel_subset_carrier a)

/-- Finitization of inclusion, following (6.3).

The first disjunct is the exceptional empty/empty case.  In the nonempty
case we require inclusion of the whole finite carrier and inclusion of the
maximal levels.  The height inequality is an explicit redundant invariant
which will be discharged when comparing this relation with (6.3). -/
def leFin (a b : Σ n, Approx ι n) : Prop :=
  (a.1 = 0 ∧ b.1 = 0) ∨
    (0 < a.1 ∧ a.1 ≤ b.1 ∧
      approxCarrier a.2 ⊆ approxCarrier b.2 ∧
      approxMaxLevel a.2 ⊆ approxMaxLevel b.2)

theorem leFin_refl (a : Σ n, Approx ι n) :
    leFin a a := by
  by_cases h0 : a.1 = 0
  · exact Or.inl ⟨h0, h0⟩
  · exact Or.inr
      ⟨Nat.pos_of_ne_zero h0, le_rfl, fun _ h => h, fun _ h => h⟩

theorem leFin_trans {a b c : Σ n, Approx ι n} :
    leFin a b → leFin b c → leFin a c := by
  intro hab hbc
  rcases hab with hab0 | habp
  · rcases hbc with hbc0 | hbcp
    · exact Or.inl ⟨hab0.1, hbc0.2⟩
    · exfalso
      omega
  · rcases hbc with hbc0 | hbcp
    · exfalso
      omega
    · exact Or.inr
        ⟨habp.1, habp.2.1.trans hbcp.2.1,
          habp.2.2.1.trans hbcp.2.2.1,
          habp.2.2.2.trans hbcp.2.2.2⟩

end StrongTreeSpace
end Milliken
