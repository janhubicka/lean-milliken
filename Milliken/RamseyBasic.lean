import Milliken.Tree
import RamseySpace.Basic

/-!
# The approximation system of strong subtrees

Finite approximations are restrictions of a strong embedding to all source
nodes of height below `n`.  As in the classical Ellentuck formalization,
we subtype the finite maps by realizability; this makes A.1 surjectivity
literal and keeps the approximation interface source-faithful.
-/

namespace Milliken

universe u

namespace StrongTreeSpace

variable (ι : Type u)

/-- Reduction of strong subtrees: `X ≤ Y` iff the embedding `X` factors
through `Y`.  This is exactly inclusion of strong subtrees, with the
canonical factor retained. -/
def le (X Y : StrongEmbedding ι) : Prop :=
  ∃ Z : StrongEmbedding ι, X = StrongEmbedding.comp Y Z

theorem le_refl (X : StrongEmbedding ι) : le ι X X :=
  ⟨StrongEmbedding.id, by simp⟩

theorem le_trans {X Y Z : StrongEmbedding ι} :
    le ι X Y → le ι Y Z → le ι X Z := by
  rintro ⟨A, rfl⟩ ⟨B, rfl⟩
  refine ⟨StrongEmbedding.comp B A, ?_⟩
  exact StrongEmbedding.comp_assoc Z B A

/-- Source nodes occurring in the first `n` levels. -/
def FiniteNode (n : ℕ) :=
  {s : Node ι // s.length < n}

/-- A realized finite strong-tree approximation of height `n`. -/
def Approx (n : ℕ) :=
  {a : FiniteNode ι n → Node ι //
    ∃ X : StrongEmbedding ι, ∀ s, X.toFun s.1 = a s}

/-- Restriction of an infinite strong subtree to its first `n` source
levels. -/
def approx (n : ℕ) (X : StrongEmbedding ι) : Approx ι n :=
  ⟨fun s => X.toFun s.1, ⟨X, fun _ => rfl⟩⟩

theorem approx_surjective (n : ℕ) :
    Function.Surjective (approx ι n) := by
  intro a
  rcases a.2 with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  apply Subtype.ext
  funext s
  exact hX s

def empty : Approx ι 0 :=
  approx ι 0 StrongEmbedding.id

theorem approx_zero (X : StrongEmbedding ι) :
    approx ι 0 X = empty ι := by
  apply Subtype.ext
  funext s
  exact (Nat.not_lt_zero _ s.2).elim

theorem separated {X Y : StrongEmbedding ι}
    (h : ∀ n, approx ι n X = approx ι n Y) :
    X = Y := by
  ext s
  let sn : FiniteNode ι (s.length + 1) :=
    ⟨s, Nat.lt_succ_self _⟩
  have hs := congrArg
    (fun a : Approx ι (s.length + 1) => a.1 sn)
    (h (s.length + 1))
  exact hs

theorem coherent {X Y : StrongEmbedding ι} {n : ℕ}
    (h : approx ι n X = approx ι n Y) :
    ∀ m, m < n → approx ι m X = approx ι m Y := by
  intro m hmn
  apply Subtype.ext
  funext s
  let sn : FiniteNode ι n := ⟨s.1, lt_trans s.2 hmn⟩
  have hs := congrArg (fun a : Approx ι n => a.1 sn) h
  exact hs

/-- A.1 for the homogeneous strong-subtree space. -/
def approximationSystem : RamseySpace.ApproximationSystem where
  Point := StrongEmbedding ι
  Approx := Approx ι
  le := le ι
  le_refl := le_refl ι
  le_trans := le_trans (ι := ι)
  approx := approx ι
  approx_surjective := approx_surjective ι
  empty := empty ι
  approx_zero := approx_zero ι
  separated := separated ι
  coherent := coherent ι

end StrongTreeSpace

end Milliken
