import Milliken.HalpernLauchli.SelectedLevelTree

/-!
# Shifting a selected-level tree above a cone

A cone above a node on selected rank m has the same branching pattern as a
new selected-level tree whose nth level is

  S.levels (m+n) - S.levels m.

This file records the shift and the elementary append/drop equivalence
between nodes of the shifted tree and nodes in the original cone.  It is the
interface needed to invoke the induction hypothesis locally in the
variable-branching Chapter 3 proof.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- Selected levels seen from rank m. -/
def shift (S : Selection) (m : ℕ) : Selection where
  levels := fun n => S.levels (m + n) - S.levels m
  zero := by simp
  strictMono := by
    intro a b hab
    have hbase :
        S.levels m ≤ S.levels (m + a) :=
      S.strictMono.monotone (by omega)
    have hlt :
        S.levels (m + a) < S.levels (m + b) :=
      S.strictMono (by omega)
    exact Nat.sub_lt_sub_right hbase hlt

@[simp] theorem shift_levels
    (S : Selection) (m n : ℕ) :
    (shift S m).levels n =
      S.levels (m + n) - S.levels m := rfl

theorem level_add_shift
    (S : Selection) (m n : ℕ) :
    S.levels m + (shift S m).levels n =
      S.levels (m + n) := by
  rw [shift_levels]
  exact Nat.add_sub_of_le
    (S.strictMono.monotone (by omega))

/-- Append a shifted-tree node after a fixed cone root. -/
def appendShifted
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (t : NodeAt (ι := ι) (shift S m) n) :
    NodeAt (ι := ι) S (m + n) := by
  refine ⟨x.1 ++ t.1, ?_⟩
  rw [List.length_append, x.2, t.2]
  exact level_add_shift S m n

theorem appendShifted_prefix
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (t : NodeAt (ι := ι) (shift S m) n) :
    x.1.IsPrefix (appendShifted S x t).1 := by
  exact List.prefix_append _ _

/-- Remove the fixed selected-level cone root from a later node. -/
def dropToShifted
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (z : NodeAt (ι := ι) S (m + n))
    (hxz : x.1.IsPrefix z.1) :
    NodeAt (ι := ι) (shift S m) n := by
  refine ⟨z.1.drop x.1.length, ?_⟩
  rw [List.length_drop, z.2, x.2, shift_levels]

theorem append_dropToShifted
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (z : NodeAt (ι := ι) S (m + n))
    (hxz : x.1.IsPrefix z.1) :
    (appendShifted S x
      (dropToShifted S x z hxz)).1 = z.1 := by
  change x.1 ++ z.1.drop x.1.length = z.1
  have htake :
      z.1.take x.1.length = x.1 :=
    (List.prefix_iff_eq_take.mp hxz).symm
  simpa [htake] using
    (List.take_append_drop x.1.length z.1)

theorem drop_appendShifted
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (t : NodeAt (ι := ι) (shift S m) n) :
    (dropToShifted S x (appendShifted S x t)
      (appendShifted_prefix S x t)).1 = t.1 := by
  change (x.1 ++ t.1).drop x.1.length = t.1
  exact List.drop_left

/-- Appending the same cone root preserves and reflects the prefix order. -/
theorem appendShifted_prefix_iff
    (S : Selection) {m p q : ℕ}
    (x : NodeAt (ι := ι) S m)
    (s : NodeAt (ι := ι) (shift S m) p)
    (t : NodeAt (ι := ι) (shift S m) q) :
    (appendShifted S x s).1.IsPrefix
        (appendShifted S x t).1 ↔
      s.1.IsPrefix t.1 := by
  change (x.1 ++ s.1).IsPrefix (x.1 ++ t.1) ↔
    s.1.IsPrefix t.1
  constructor
  · exact StrongEmbedding.prefix_cancel_left x.1
  · exact StrongEmbedding.prefix_append_left x.1

/-- A prefix relation inside the original cone becomes a prefix relation
between the corresponding shifted tails. -/
theorem dropToShifted_prefix
    (S : Selection) {m p q : ℕ}
    (hpq : p ≤ q)
    (x : NodeAt (ι := ι) S m)
    (y : NodeAt (ι := ι) S (m + p))
    (z : NodeAt (ι := ι) S (m + q))
    (hxy : x.1.IsPrefix y.1)
    (hxz : x.1.IsPrefix z.1)
    (hyz : y.1.IsPrefix z.1) :
    (dropToShifted S x y hxy).1.IsPrefix
      (dropToShifted S x z hxz).1 := by
  exact hyz.drop x.1.length

/-- Appending after dropping the fixed cone root recovers the original
selected-level node as a subtype. -/
theorem append_dropToShifted_eq
    (S : Selection) {m n : ℕ}
    (x : NodeAt (ι := ι) S m)
    (z : NodeAt (ι := ι) S (m + n))
    (hxz : x.1.IsPrefix z.1) :
    appendShifted S x (dropToShifted S x z hxz) = z := by
  apply Subtype.ext
  exact append_dropToShifted S x z hxz

end SelectedLevelTree
end HalpernLauchli
end Milliken
