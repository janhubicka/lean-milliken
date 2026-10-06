import Milliken.HalpernLauchli.Lemma316Fill

/-!
# Highly dense sets exclude one fixed arbitrarily dense complement cone

A useful replacement for the level-thinning shorthand in Remark 3.8 is the
following elementary consequence of the definition of `HighlyDense`.

If the complement of `P` contained matrices of arbitrarily large density
above one fixed base vector, complete such a local matrix outside the base
cones.  The resulting global dense matrix would force `P` to meet the
original local matrix, contradicting its containment in the complement.

This obstruction is stronger than the single somewhere-dense witness used
in the reduced statement, and is the form naturally produced when the
Lemma 3.15 contradiction is run to arbitrarily deep finite fronts.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A set contains matrices of every density scale above one fixed (not
necessarily level) base vector. -/
def ContainsArbitrarilyDenseAbove {d : ℕ}
    (P : Set (Fin d → Node ι)) : Prop :=
  ∃ base : Fin d → Node ι,
    ∀ q : ℕ, ∃ M : Matrix ι d,
      M.DenseAbove base q ∧ M.carrier ⊆ P

/-- A highly dense set cannot have an arbitrarily dense complement above a
fixed base vector. -/
theorem no_arbitrarilyDenseAbove_compl_of_highlyDense
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    {P : Set (Fin d → Node ι)}
    (hP : HighlyDense P) :
    ¬ ContainsArbitrarilyDenseAbove Pᶜ := by
  classical
  rintro ⟨base, hbad⟩
  let r : ℕ :=
    Finset.univ.sup (fun i : Fin d => (base i).length)
  have hbase_r : ∀ i : Fin d, (base i).length ≤ r := by
    intro i
    dsimp [r]
    exact Finset.le_sup
      (f := fun j : Fin d => (base j).length)
      (Finset.mem_univ i)
  rcases hP r with ⟨n, hn⟩
  let q : ℕ := max n (r + 1)
  rcases hbad q with ⟨M, hMdense, hMsub⟩
  have hnq : n ≤ q := by
    dsimp [q]
    exact Nat.le_max_left _ _
  have hrq : r < q := by
    dsimp [q]
    exact (Nat.lt_succ_self r).trans_le
      (Nat.le_max_right n (r + 1))
  have hbase_q : ∀ i, (base i).length < q := by
    intro i
    exact (hbase_r i).trans_lt hrq
  let A : Matrix ι d :=
    M.fillOutsideAbove base q
  have hAq : A.DenseAt q := by
    dsimp [A]
    exact M.fillOutsideAbove_denseAt
      base hMdense hbase_q le_rfl
  have hAn : A.DenseAt n :=
    A.denseAt_of_le hnq hAq
  have hPA :
      ProductDenseAt (P ∩ A.carrier) r :=
    hn A hAn
  let x : Fin d → Node ι :=
    fun i => extendToLevel (base i) r
  have hxlevel : IsLevelVectorAt r x := by
    intro i
    dsimp [x]
    exact length_extendToLevel (hbase_r i)
  rcases hPA x hxlevel with
    ⟨y, hyPA, hxy⟩
  have hbase_y :
      ∀ i, (base i).IsPrefix (y i) := by
    intro i
    exact
      (prefix_extendToLevel (base i) r).trans
        (hxy i)
  have hyM : y ∈ M.carrier := by
    dsimp [A] at hyPA
    exact M.carrier_mem_of_fillOutsideAbove_of_prefix
      base hyPA.2 hbase_y
  exact (hMsub hyM) hyPA.1

end HalpernLauchli
end Milliken
