import Milliken.GeneralTree.HeterogeneousConeDensity

/-!
# Highly dense heterogeneous products forbid arbitrarily dense bad cones

This is the source-faithful heterogeneous version of the main
obstruction lemma in Todorčević's Chapter 3 (§3.2).

Assume a set Q of product nodes is highly dense. A fixed product
cone cannot contain complement-colour matrices of arbitrarily large
density: choose a level r above the finitely many coordinate roots;
choose q large enough for high density; complete a q-dense matrix
inside the bad cone to a globally dense matrix by filling all the
source-level nodes outside the cone. High density then produces a
Q-tuple above the original base. It necessarily belongs to the
complement-colour cone matrix, a contradiction.

Only the local finiteness and strongness of each heterogeneous
coordinate tree enter. No fixed global branching degree or
word alphabet is assumed.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}
variable (P : Fin d → StrongSubtree U)

/-- Arbitrarily dense coordinate matrices in the descendant cones
of one fixed coordinate tuple. The base itself belongs to the
appropriate input strong trees. -/
def HeterogeneousContainsArbitrarilyDenseAbove
    (Q : Set (Fin d → U)) : Prop :=
  ∃ base : Fin d → U,
    (∀ i, base i ∈ (P i).carrier) ∧
      ∀ q : ℕ, ∃ M : HeterogeneousMatrix P,
        M.DenseAbove base q ∧ M.carrier ⊆ Q

/-- Todorčević's high-density obstruction, for *arbitrary*
pruned locally finitely branching heterogeneous input trees:
the complement of a highly dense set cannot contain
matrices of every density scale above a single fixed base tuple. -/
theorem no_arbitrarilyDenseAbove_compl_of_heterogeneousHighlyDense
    (Q : Set (Fin d → U))
    (hQ : HeterogeneousHighlyDense P Q) :
    ¬ HeterogeneousContainsArbitrarilyDenseAbove P Qᶜ := by
  classical
  rintro ⟨base, hbase, hbad⟩
  let rank : Fin d → ℕ :=
    fun i => Classical.choose
      ((P i).carrier_levels (base i) (hbase i))
  have hrank (i : Fin d) :
      U.level (base i) = (P i).levels (rank i) :=
    Classical.choose_spec
      ((P i).carrier_levels (base i) (hbase i))
  let r : ℕ := Finset.univ.sup rank
  have hrank_le (i : Fin d) : rank i ≤ r := by
    dsimp [r]
    exact Finset.le_sup (f := rank) (Finset.mem_univ i)
  have hbaseRank (i : Fin d) :
      base i ∈ (P i).sourceLevel (rank i) :=
    ⟨hbase i, hrank i⟩
  have hExt (i : Fin d) :
      ∃ z : U,
        z ∈ (P i).sourceLevel r ∧ base i ≤ z :=
    (P i).exists_sourceLevel_descendant
      (hrank_le i) (hbaseRank i)
  let x : Fin d → U := fun i => Classical.choose (hExt i)
  have hxlevel (i : Fin d) :
      x i ∈ (P i).sourceLevel r :=
    (Classical.choose_spec (hExt i)).1
  have hbase_x (i : Fin d) : base i ≤ x i :=
    (Classical.choose_spec (hExt i)).2
  let xLevel : HeterogeneousLevelTuple P r :=
    ⟨x, hxlevel⟩
  obtain ⟨m, hm⟩ := hQ r
  let q : ℕ := max m (r + 1)
  have hmq : m ≤ q := Nat.le_max_left m (r + 1)
  obtain ⟨M, hMdense, hMbad⟩ := hbad q
  let A : HeterogeneousMatrix P :=
    M.fillOutsideAbove base q
  have hAdense : A.DenseAt q :=
    M.fillOutsideAbove_denseAt base q hMdense
  have hAm : A.DenseAt m :=
    A.denseAt_of_le hmq hAdense
  have hQprod :
      HeterogeneousProductDenseAt P
        (Q ∩ A.carrier) r :=
    hm A hAm
  obtain ⟨y, hyQA, hxy⟩ := hQprod xLevel
  have hbase_y (i : Fin d) : base i ≤ y i :=
    (hbase_x i).trans (hxy i)
  have hyM : y ∈ M.carrier :=
    M.mem_carrier_of_fillOutsideAbove_of_above
      base q hyQA.2 hbase_y
  exact (hMbad hyM) hyQA.1

end GeneralTree
end Milliken
