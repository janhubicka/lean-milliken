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


/-- For a fixed finite target set there are only finitely many realized
approximations of a fixed height whose carrier is contained in that set. -/
theorem boundedApprox_finite [Finite ι] {n : ℕ}
    {S : Set (Node ι)} (hS : S.Finite) :
    {a : Approx ι n | approxCarrier a ⊆ S}.Finite := by
  letI : Finite (FiniteNode ι n) := finite_finiteNode (ι := ι) n
  letI : Finite S := hS.to_subtype
  let encode :
      {a : Approx ι n // approxCarrier a ⊆ S} →
        (FiniteNode ι n → S) :=
    fun a s => ⟨a.1.1 s, a.2 ⟨s, rfl⟩⟩
  have hencode : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    funext s
    exact congrArg Subtype.val (congrFun hab s)
  exact Finite.of_injective encode hencode

/-- The lower cone of any finite approximation is finite.  This is the
finiteness clause of A.2. -/
theorem leFin_lowerFinite [Finite ι] (b : Σ n, Approx ι n) :
    Set.Finite {a | leFin a b} := by
  classical
  let S : Set (Node ι) := approxCarrier b.2
  have hS : S.Finite := approxCarrier_finite b.2
  let Bounded :=
    Σ i : Fin (b.1 + 1),
      {a : Approx ι i.1 // approxCarrier a ⊆ S}
  letI : ∀ i : Fin (b.1 + 1),
      Finite {a : Approx ι i.1 // approxCarrier a ⊆ S} :=
    fun i => (boundedApprox_finite (ι := ι) (n := i.1) hS).to_subtype
  letI : Finite Bounded := inferInstance
  let forget : Bounded → (Σ n, Approx ι n) :=
    fun q => ⟨q.1.1, q.2.1⟩
  apply (Set.finite_range forget).subset
  intro a ha
  have hheight : a.1 ≤ b.1 := by
    rcases ha with h0 | hp
    · omega
    · exact hp.2.1
  have hsub : approxCarrier a.2 ⊆ S := by
    rcases ha with h0 | hp
    · intro x hx
      rcases hx with ⟨s, rfl⟩
      have hs : s.1.length < a.1 := s.2
      omega
    · exact hp.2.2.1
  let i : Fin (b.1 + 1) := ⟨a.1, Nat.lt_succ_of_le hheight⟩
  let q : Bounded := ⟨i, ⟨a.2, hsub⟩⟩
  exact ⟨q, rfl⟩

end StrongTreeSpace
end Milliken
