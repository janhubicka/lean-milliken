import Milliken.Factor

/-!
# Completion of A.2

This file proves that the finite carrier relation realizes the infinite
factorization order.  The forward direction reads off a large enough level
of the factor embedding; the reverse direction turns finite carrier
inclusions into global range inclusion and then invokes the factorization
theorem.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- The zeroth approximation has empty carrier. -/
theorem approxCarrier_zero (X : StrongEmbedding ι) :
    approxCarrier (approx ι 0 X) = ∅ := by
  ext x
  constructor
  · rintro ⟨s, hs⟩
    exact (Nat.not_lt_zero _ s.2).elim
  · simp

/-- A factorization gives finite carrier inclusion at a sufficiently large
target level. -/
theorem exists_leFin_approx_of_le [Nonempty ι]
    {X Y : StrongEmbedding ι} (hXY : le ι X Y) (n : ℕ) :
    ∃ m,
      leFin ((S ι).finiteApprox n X)
        ((S ι).finiteApprox m Y) := by
  rcases hXY with ⟨Z, rfl⟩
  cases n with
  | zero =>
      refine ⟨0, ?_⟩
      constructor
      · exact le_rfl
      · rw [approxCarrier_zero, approxCarrier_zero]
  | succ k =>
      rcases Z.level_witness with ⟨lev, hlev, hZlev⟩
      let m := lev k + 1
      refine ⟨m, ?_⟩
      constructor
      · dsimp [m]
        have hk : k ≤ lev k := StrictMono.id_le hlev k
        omega
      · rintro x ⟨s, rfl⟩
        let t : FiniteNode ι m :=
          ⟨Z.toFun s.1, by
            rw [hZlev]
            have hsk : s.1.length ≤ k := by omega
            exact Nat.lt_succ_of_le (hlev.monotone hsk)⟩
        exact ⟨t, rfl⟩

/-- Finite carrier inclusions at every source height imply global range
inclusion. -/
theorem range_subset_of_forall_leFin_approx
    {X Y : StrongEmbedding ι}
    (h :
      ∀ n, ∃ m,
        leFin ((S ι).finiteApprox n X)
          ((S ι).finiteApprox m Y)) :
    StrongEmbedding.range X ⊆ StrongEmbedding.range Y := by
  rintro x ⟨s, rfl⟩
  rcases h (s.length + 1) with ⟨m, hm⟩
  have hx :
      X.toFun s ∈ approxCarrier (approx ι (s.length + 1) X) := by
    exact ⟨⟨s, Nat.lt_succ_self _⟩, rfl⟩
  rcases hm.2 hx with ⟨t, ht⟩
  exact ⟨t.1, ht⟩

/-- A.2(2): the finite relation realizes the infinite reduction order. -/
theorem realizesOrder [Nonempty ι]
    (X Y : StrongEmbedding ι) :
    le ι X Y ↔
      ∀ n, ∃ m,
        leFin ((S ι).finiteApprox n X)
          ((S ι).finiteApprox m Y) := by
  constructor
  · intro hXY n
    exact exists_leFin_approx_of_le hXY n
  · intro h
    exact (le_iff_range_subset X Y).2
      (range_subset_of_forall_leFin_approx h)

/-- Todorčević A.2 for the homogeneous strong-subtree space. -/
def finitization [Finite ι] [Nonempty ι] :
    RamseySpace.Finitization (S ι) where
  leFin := leFin
  leFin_refl := leFin_refl
  leFin_trans := leFin_trans
  lowerFinite := lowerFinite
  realizesOrder := realizesOrder
  prefix_leFin := prefix_leFin

end StrongTreeSpace
end Milliken
