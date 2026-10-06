import Milliken.HalpernLauchli.Remark38

/-!
# The tree carried by a selected sequence of levels

For the unbounded-gap case of Remark 3.8 we should not pretend that the
compressed tree is homogeneous.  Its nodes on source level `n` are exactly
the ambient words whose length is the selected level `levels n`.  The
immediate successors of such a node are all of its extensions on the next
selected level; this is a finite, nonempty set, but its cardinality may
depend on `n`.

This file packages that elementary tree geometry.  It is deliberately
independent of the Ramsey argument so that the remaining Chapter 3 proof can
be generalized against this interface rather than against a fixed alphabet.
-/

namespace Milliken
namespace HalpernLauchli
namespace SelectedLevelTree

universe u
variable {ι : Type u}

/-- A strictly increasing selected-level sequence starting at the root. -/
structure Selection where
  levels : ℕ → ℕ
  zero : levels 0 = 0
  strictMono : StrictMono levels

/-- Ambient nodes lying on one selected level. -/
def NodeAt (S : Selection) (n : ℕ) :=
  {s : Node ι // s.length = S.levels n}

instance nodeAtFinite
    [Finite ι] (S : Selection) (n : ℕ) :
    Finite (NodeAt (ι := ι) S n) :=
  (List.finite_length_eq ι (S.levels n)).to_subtype

noncomputable instance nodeAtNonempty
    [Nonempty ι] (S : Selection) (n : ℕ) :
    Nonempty (NodeAt (ι := ι) S n) :=
  ⟨⟨rayNode (ι := ι) (S.levels n),
    rayNode_length (ι := ι) (S.levels n)⟩⟩

/-- The root node on selected level zero. -/
def root (S : Selection) :
    NodeAt (ι := ι) S 0 :=
  ⟨[], by simp [S.zero]⟩

/-- Immediate successors in the compressed selected-level tree. -/
def Child
    (S : Selection) {n : ℕ}
    (x : NodeAt (ι := ι) S n) :=
  {y : NodeAt (ι := ι) S (n + 1) //
    x.1.IsPrefix y.1}

instance childFinite
    [Finite ι]
    (S : Selection) {n : ℕ}
    (x : NodeAt (ι := ι) S n) :
    Finite (Child S x) := by
  letI : Finite (NodeAt (ι := ι) S (n + 1)) :=
    nodeAtFinite S (n + 1)
  apply Finite.of_injective
    (fun y : Child S x => y.1)
  intro a b hab
  exact Subtype.ext hab

/-- Canonical extension of a selected-level node to the next selected
level. -/
noncomputable def childWitness
    [Nonempty ι]
    (S : Selection) {n : ℕ}
    (x : NodeAt (ι := ι) S n) :
    NodeAt (ι := ι) S (n + 1) := by
  let y : Node ι :=
    extendToLevel x.1 (S.levels (n + 1))
  have hle :
      x.1.length ≤ S.levels (n + 1) := by
    rw [x.2]
    exact S.strictMono.monotone (Nat.le_succ n)
  exact ⟨y, by
    dsimp [y]
    exact length_extendToLevel hle⟩

theorem prefix_childWitness
    [Nonempty ι]
    (S : Selection) {n : ℕ}
    (x : NodeAt (ι := ι) S n) :
    x.1.IsPrefix (childWitness S x).1 := by
  unfold childWitness
  exact prefix_extendToLevel _ _

/-- Every node in the compressed tree has an immediate successor. -/
theorem child_nonempty
    [Nonempty ι]
    (S : Selection) {n : ℕ}
    (x : NodeAt (ι := ι) S n) :
    Nonempty (Child S x) :=
  ⟨⟨childWitness S x, prefix_childWitness S x⟩⟩

/-- Truncate a later selected-level node to an earlier selected level. -/
def truncate
    (S : Selection)
    {m n : ℕ} (hmn : m ≤ n)
    (z : NodeAt (ι := ι) S n) :
    NodeAt (ι := ι) S m := by
  let t : Node ι := z.1.take (S.levels m)
  have hle :
      S.levels m ≤ z.1.length := by
    rw [z.2]
    exact S.strictMono.monotone hmn
  exact ⟨t, by
    dsimp [t]
    exact List.length_take_of_le hle⟩

theorem truncate_val
    (S : Selection)
    {m n : ℕ} (hmn : m ≤ n)
    (z : NodeAt (ι := ι) S n) :
    (truncate S hmn z).1 =
      z.1.take (S.levels m) := rfl

theorem truncate_prefix
    (S : Selection)
    {m n : ℕ} (hmn : m ≤ n)
    (z : NodeAt (ι := ι) S n) :
    (truncate S hmn z).1.IsPrefix z.1 := by
  rw [truncate_val]
  exact List.take_prefix _ _

/-- If an earlier selected-level node is below a later one, it is exactly
the selected-level truncation of the later node. -/
theorem truncate_eq_of_prefix
    (S : Selection)
    {m n : ℕ} (hmn : m ≤ n)
    (x : NodeAt (ι := ι) S m)
    (z : NodeAt (ι := ι) S n)
    (hxz : x.1.IsPrefix z.1) :
    truncate S hmn z = x := by
  apply Subtype.ext
  rw [truncate_val]
  have h := List.prefix_iff_eq_take.mp hxz
  rw [x.2] at h
  exact h.symm

/-- Every extension reaching a later selected level passes through a unique
next-level prefix; existence is the part needed by the Ramsey proof. -/
theorem exists_child_below
    (S : Selection)
    {n q : ℕ} (hnq : n < q)
    (x : NodeAt (ι := ι) S n)
    (z : NodeAt (ι := ι) S q)
    (hxz : x.1.IsPrefix z.1) :
    ∃ y : Child S x, y.1.1.IsPrefix z.1 := by
  have hsucc : n + 1 ≤ q := Nat.succ_le_of_lt hnq
  let y0 : NodeAt (ι := ι) S (n + 1) :=
    truncate S hsucc z
  have hxlen :
      x.1.length ≤ S.levels (n + 1) := by
    rw [x.2]
    exact S.strictMono.monotone (Nat.le_succ n)
  have htake := hxz.take (S.levels (n + 1))
  have hxself :
      x.1.take (S.levels (n + 1)) = x.1 :=
    (List.take_eq_self_iff _).2 hxlen
  rw [hxself] at htake
  have hxy : x.1.IsPrefix y0.1 := by
    dsimp [y0]
    exact htake
  let y : Child S x := ⟨y0, hxy⟩
  refine ⟨y, ?_⟩
  dsimp [y, y0]
  exact truncate_prefix S hsucc z

/-- The level selection produced from a highly dense set in Remark 3.8. -/
noncomputable def remark38Selection
    {d : ℕ} {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) (k : ℕ) :
    Selection where
  levels := remark38Levels hP k
  zero := remark38Levels_zero hP k
  strictMono := remark38Levels_strictMono hP k

end SelectedLevelTree
end HalpernLauchli
end Milliken
