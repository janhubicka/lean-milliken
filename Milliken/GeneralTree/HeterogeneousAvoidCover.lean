import Milliken.GeneralTree.HeterogeneousBadSections

/-!
# Minimal finite avoiding covers in heterogeneous products

The selected source level-k product of arbitrary pruned locally
finitely branching input strong trees is finite, even with
unbounded node-dependent branching degrees. Consequently the
bad-section cones in the first part of Todorčević Lemma 3.15
admit a finite cover, and among all such covers there is one
of smallest cardinality.

This module exposes the last-coordinate cone-density predicate,
its elementary restriction law, the finite avoiding-cover structure
and the minimal-cover existence theorem. These are unconditional
combinatorial facts: higher-dimensional HDHL is not assumed here.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Y is dense in the retained last-coordinate strong tree
inside the cone rooted at t, relative to that tree's carrier. -/
def HeterogeneousConeDense
    (T : StrongSubtree U) (Y : Set U) (t : U) : Prop :=
  ∀ z ∈ T.carrier, t ≤ z →
    ∃ y ∈ Y, z ≤ y

/-- A set is somewhere cone-dense in the actual strong tree. -/
def HeterogeneousSomewhereConeDense
    (T : StrongSubtree U) (Y : Set U) : Prop :=
  ∃ t : U, t ∈ T.carrier ∧
    HeterogeneousConeDense T Y t

/-- Retain only elements of Y in the ambient cone above t. -/
def heterogeneousRestrictCone (Y : Set U) (t : U) : Set U :=
  {y | y ∈ Y ∧ t ≤ y}

/-- Passing to a deeper cone preserves relative cone density. -/
theorem heterogeneousConeDense_restrict
    (T : StrongSubtree U) (Y : Set U)
    {t u : U}
    (hY : HeterogeneousConeDense T Y t)
    (htu : t ≤ u) :
    HeterogeneousConeDense
      T (heterogeneousRestrictCone Y u) u := by
  intro z hz huz
  obtain ⟨y, hyY, hzy⟩ :=
    hY z hz (htu.trans huz)
  exact ⟨y, ⟨hyY, huz.trans hzy⟩, hzy⟩

/-- The finite family of level-k tuples accounting for all
bad last-coordinate sections on a cone-dense Y. -/
structure HeterogeneousAvoidCover
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) (X : Set U) where
  D : Finset (HeterogeneousLevelTuple
    (fun i : Fin d => P i.castSucc) k)
  n0 : ℕ
  Y : Set U
  root : U
  root_mem : root ∈ (P (Fin.last d)).carrier
  Y_subset : Y ⊆ X
  Y_inside : Y ⊆ (P (Fin.last d)).carrier
  Y_dense : HeterogeneousConeDense
    (P (Fin.last d)) Y root
  cover :
    ∀ n, n0 ≤ n →
      ∀ y ∈ Y, HeterogeneousBadSectionAt P Q k n y →
        ∃ x ∈ D,
          HeterogeneousSectionAvoidAt P Q y x.1 n

/-- The full finite source-level product provides an initial
avoiding cover, without any pigeonhole assumption. -/
theorem exists_heterogeneousAvoidCover
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {X : Set U}
    (hXinside : X ⊆ (P (Fin.last d)).carrier)
    (hXsome : HeterogeneousSomewhereConeDense
      (P (Fin.last d)) X) :
    Nonempty (HeterogeneousAvoidCover P Q k X) := by
  classical
  let Front : Fin d → StrongSubtree U :=
    fun i => P i.castSucc
  letI : Fintype (HeterogeneousLevelTuple Front k) :=
    Fintype.ofFinite _
  obtain ⟨root, hroot, hrootDense⟩ := hXsome
  refine ⟨{
    D := Finset.univ
    n0 := k + 1
    Y := X
    root := root
    root_mem := hroot
    Y_subset := fun _ h => h
    Y_inside := hXinside
    Y_dense := hrootDense
    cover := ?_
  }⟩
  intro n hn y hy hbad
  have hkn : k < n := by omega
  obtain ⟨x, hAvoid⟩ :=
    heterogeneousBadSectionAt_has_avoidWitness
      P Q hkn hbad
  exact ⟨x, Finset.mem_univ x, hAvoid⟩

/-- Choose an avoiding cover with the smallest number of
finite level-k tuple witnesses. -/
theorem exists_minimalHeterogeneousAvoidCover
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {X : Set U}
    (hXinside : X ⊆ (P (Fin.last d)).carrier)
    (hXsome : HeterogeneousSomewhereConeDense
      (P (Fin.last d)) X) :
    ∃ C : HeterogeneousAvoidCover P Q k X,
      ∀ C' : HeterogeneousAvoidCover P Q k X,
        C.D.card ≤ C'.D.card := by
  classical
  let C0 : HeterogeneousAvoidCover P Q k X :=
    Classical.choice
      (exists_heterogeneousAvoidCover P Q k hXinside hXsome)
  let criterion : ℕ → Prop :=
    fun m => ∃ C : HeterogeneousAvoidCover P Q k X,
      C.D.card = m
  have hcriterion : ∃ m, criterion m :=
    ⟨C0.D.card, C0, rfl⟩
  let m : ℕ := Nat.find hcriterion
  obtain ⟨C, hC⟩ := Nat.find_spec hcriterion
  refine ⟨C, ?_⟩
  intro C'
  rw [hC]
  by_contra hle
  have hlt : C'.D.card < m :=
    Nat.lt_of_not_ge hle
  exact (Nat.find_min hcriterion hlt) ⟨C', rfl⟩

end GeneralTree
end Milliken
