import Milliken.AmbientChild
import Milliken.GeneralTree.ThinningAncestry

/-!
# Preserving all consecutive selected source levels under thinning

Suppose B is an arbitrary pruned locally finitely branching strong
tree and f : ℕ → ℕ is strictly increasing with f(0)=0.
If f(k+1)=f(k)+1 and the recursively thinned k-th source
level contains *all* of B's selected source level f(k), then
the next thinned level also contains all of B's level f(k+1).

Indeed every node z on the latter level has a selected predecessor
p at the former, and the first ambient child on the branch p<z
identifies a child cone whose chosen representative must be z
by B's successor uniqueness. This also proves a complete
initial prefix is preserved whenever f is the identity there.

This is a prerequisite for preserving the entire depth-d prefix
of B in the protected A.3(2) mixed-cone construction.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- For two *consecutive* selected source levels of B, the
canonical long-cone choice is the unique actual B-successor. -/
theorem longConeRepresentative_eq_next
    (B : StrongSubtree U)
    {m : ℕ} {x : U} (hx : x ∈ B.sourceLevel m)
    (y : ChildIndex U x)
    {z : U} (hz : z ∈ B.sourceLevel (m + 1))
    (hyz : (y : U) ≤ z) :
    B.longConeRepresentative (Nat.lt_succ_self m) hx y = z := by
  let rep : U :=
    B.longConeRepresentative (Nat.lt_succ_self m) hx y
  have hrep := B.longConeRepresentative_spec
    (Nat.lt_succ_self m) hx y
  obtain ⟨w, hw, hunique⟩ :=
    B.successor_unique m x hx.1 hx.2 y.1 y.2
  have hrepw : rep = w :=
    hunique rep ⟨hrep.1.1, hrep.1.2, hrep.2⟩
  have hzw : z = w := hunique z ⟨hz.1, hz.2, hyz⟩
  exact hrepw.trans hzw.symm

/-- A complete thinning level stays complete when f makes one
consecutive selected-level step. -/
theorem thinningLevel_full_succ
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (k : ℕ)
    (hstep : f (k + 1) = f k + 1)
    (hfull : B.thinningLevel f hf hf0 k =
      B.sourceLevel (f k)) :
    B.thinningLevel f hf hf0 (k + 1) =
      B.sourceLevel (f (k + 1)) := by
  ext z
  constructor
  · intro hz
    exact B.thinningLevel_subset_sourceLevel f hf hf0 (k + 1) hz
  · intro hz
    have hzNext : z ∈ B.sourceLevel (f k + 1) := by
      simpa only [hstep] using hz
    obtain ⟨p, hp, hpl, hpz⟩ :=
      B.predecessor_exists (f k) z hzNext.1 hzNext.2
    have hpRank : U.level p < U.level z := by
      calc
        U.level p = B.levels (f k) := hpl
        _ < B.levels (f k + 1) :=
          B.levels_strictMono (Nat.lt_succ_self (f k))
        _ = U.level z := hzNext.2.symm
    have hpLt : p < z := by
      rcases hpz.eq_or_lt with heq | hlt
      · have hh : U.level p = U.level z :=
          congrArg (U.level) heq
        omega
      · exact hlt
    obtain ⟨y, hpy, hyz⟩ := U.exists_child_le_of_lt hpLt
    have hpThin : p ∈ B.thinningLevel f hf hf0 k := by
      rw [hfull]
      exact ⟨hp, hpl⟩
    let yy : ChildIndex U p := ⟨y, hpy⟩
    have hpB : p ∈ B.sourceLevel (f k) :=
      B.thinningLevel_subset_sourceLevel f hf hf0 k hpThin
    have hrep :
        B.longConeRepresentative
          (hf (Nat.lt_succ_self k)) hpB yy = z := by
      simpa only [hstep] using
        (B.longConeRepresentative_eq_next hpB yy hzNext hyz)
    apply (B.thinningLevel_succ_iff f hf hf0 k z).2
    exact ⟨⟨p, hpThin⟩, yy, hrep.symm⟩

/-- Thinning preserves a full initial sequence of B-source
levels whenever f fixes that prefix pointwise. -/
theorem thinningLevel_full_prefix
    (B : StrongSubtree U)
    (f : ℕ → ℕ) (hf : StrictMono f) (hf0 : f 0 = 0)
    (n : ℕ)
    (hprefix : ∀ k : ℕ, k ≤ n → f k = k) :
    B.thinningLevel f hf hf0 n = B.sourceLevel n := by
  induction n with
  | zero =>
      calc
        B.thinningLevel f hf hf0 0 = {B.root} :=
          B.thinningLevel_zero f hf hf0
        _ = B.sourceLevel 0 :=
          (B.sourceLevel_zero_eq_singleton).symm
  | succ n ih =>
      have hprev : ∀ k : ℕ, k ≤ n → f k = k := by
        intro k hk
        exact hprefix k (by omega)
      have hfn := hprefix n (by omega)
      have hfnnext := hprefix (n + 1) (by omega)
      have hstep : f (n + 1) = f n + 1 := by omega
      have hfull : B.thinningLevel f hf hf0 n =
          B.sourceLevel (f n) := by
        rw [hfn]
        exact ih hprev
      have h := B.thinningLevel_full_succ f hf hf0
        n hstep hfull
      simpa only [hfnnext] using h

end StrongSubtree
end GeneralTree
end Milliken
