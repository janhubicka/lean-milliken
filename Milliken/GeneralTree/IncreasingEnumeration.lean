import Milliken.AmbientTree

/-!
# Increasing enumeration of an infinite set of natural numbers

An elementary selector used by heterogeneous binary Halpern–Läuchli
to choose a monochromatic infinite set of *source indices*.

This fact requires no tree, homogeneous alphabet, strong embedding,
or Ramsey-theoretic principle. It replaces the only import from
the old homogeneous `HalpernLauchli.LevelSelector` library in the
unrestricted general-tree proof.
-/

namespace Milliken
namespace GeneralTree

/-- A strictly increasing enumeration (not necessarily beginning at
the minimum) of an infinite set of source indices. -/
noncomputable def increasingEnumeration
    (A : Set ℕ) (hA : A.Infinite) : ℕ → ℕ
  | 0 => Classical.choose (hA.exists_gt 0)
  | n + 1 =>
      Classical.choose
        (hA.exists_gt (increasingEnumeration A hA n))

theorem increasingEnumeration_mem
    (A : Set ℕ) (hA : A.Infinite) (n : ℕ) :
    increasingEnumeration A hA n ∈ A := by
  cases n with
  | zero =>
      exact (Classical.choose_spec (hA.exists_gt 0)).1
  | succ n =>
      exact (Classical.choose_spec
        (hA.exists_gt (increasingEnumeration A hA n))).1

theorem increasingEnumeration_lt_succ
    (A : Set ℕ) (hA : A.Infinite) (n : ℕ) :
    increasingEnumeration A hA n <
      increasingEnumeration A hA (n + 1) := by
  exact (Classical.choose_spec
    (hA.exists_gt (increasingEnumeration A hA n))).2

theorem increasingEnumeration_strictMono
    (A : Set ℕ) (hA : A.Infinite) :
    StrictMono (increasingEnumeration A hA) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact increasingEnumeration_lt_succ A hA n

end GeneralTree
end Milliken
