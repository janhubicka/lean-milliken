import Milliken.FiniteApprox
import RamseySpace.Finitization

/-!
# A.2 for the strong-subtree space

The abstract finitization used here is source height together with inclusion
of the finite carrier.  This is deliberately separated from Todorčević's
literal relation (6.3), retained as `bookLeFin` in `FiniteApprox.lean`.

This file proves the purely finite parts of A.2 first: finite lower cones and
the compatibility with initial segments.  The realization of the infinite
order is completed through the factorization lemmas below.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

abbrev S (ι : Type u) := approximationSystem ι

/-- Approximations of one fixed height whose carrier lies in a fixed finite
set. -/
def BoundedApprox (B : Set (Node ι)) (n : ℕ) :=
  {a : Approx ι n // approxCarrier a ⊆ B}

theorem finite_boundedApprox [Finite ι]
    {B : Set (Node ι)} (hB : B.Finite) (n : ℕ) :
    Finite (BoundedApprox B n) := by
  letI : Finite (FiniteNode ι n) := finite_finiteNode (ι := ι) n
  letI : Finite B := hB.to_subtype
  let encode : BoundedApprox B n → (FiniteNode ι n → B) :=
    fun a s => ⟨a.1.1 s, a.2 ⟨s, rfl⟩⟩
  apply Finite.of_injective encode
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  funext s
  exact congrArg Subtype.val (congrFun hab s)

/-- The lower cone of a finite approximation is finite. -/
theorem lowerFinite [Finite ι]
    (b : (S ι).FiniteApprox) :
    {a | leFin a b}.Finite := by
  rw [← Set.finite_coe_iff]
  let B : Set (Node ι) := approxCarrier b.2
  have hB : B.Finite := approxCarrier_finite b.2
  let Candidate :=
    Σ n : Fin (b.1 + 1), BoundedApprox B n.1
  letI : ∀ n : Fin (b.1 + 1), Finite (BoundedApprox B n.1) :=
    fun n => finite_boundedApprox hB n.1
  letI : Finite Candidate := inferInstance
  let encode : {a : (S ι).FiniteApprox // leFin a b} → Candidate :=
    fun a =>
      ⟨⟨a.1.1, Nat.lt_succ_of_le a.2.1⟩,
        ⟨a.1.2, a.2.2⟩⟩
  exact Finite.of_injective encode (by
    intro a c hac
    apply Subtype.ext
    apply Sigma.ext
    · exact congrArg (fun q : Candidate => q.1.1) hac
    · apply Subtype.ext
      exact congrArg (fun q : Candidate => q.2.1) hac)

/-- Initial approximations have nested carriers. -/
theorem approxCarrier_subset_of_isInitial
    {n m : ℕ} {a : (S ι).Approx n} {b : (S ι).Approx m}
    (hab : (S ι).IsInitial a b) :
    approxCarrier a ⊆ approxCarrier b := by
  rcases hab with ⟨hnm, X, hXa, hXb⟩
  subst a
  subst b
  rintro x ⟨s, rfl⟩
  let t : FiniteNode ι m := ⟨s.1, lt_of_lt_of_le s.2 hnm⟩
  exact ⟨t, rfl⟩

/-- A.2(3) for the carrier finitization. -/
theorem prefix_leFin
    {n m k : ℕ}
    {a : (S ι).Approx n} {b : (S ι).Approx m} {c : (S ι).Approx k}
    (hab : (S ι).IsInitial a b)
    (hbc : leFin (⟨m, b⟩ : (S ι).FiniteApprox)
                 (⟨k, c⟩ : (S ι).FiniteApprox)) :
    ∃ (j : ℕ) (d : (S ι).Approx j),
      (S ι).IsInitial d c ∧
        leFin (⟨n, a⟩ : (S ι).FiniteApprox)
              (⟨j, d⟩ : (S ι).FiniteApprox) := by
  refine ⟨k, c, (S ι).isInitial_refl c, ?_⟩
  exact ⟨hab.1.trans hbc.1,
    (approxCarrier_subset_of_isInitial hab).trans hbc.2⟩

end StrongTreeSpace
end Milliken
