import Milliken.GeneralTree.HeterogeneousAvoidCover

/-!
# The minimum-cover density lemma in heterogeneous HDHL

This is the minimal-D step in Todorčević Lemma 3.15.
Take a cardinality-minimal finite collection D of source-level-k
front tuples witnessing all sufficiently late bad sections on a
cone-dense set Y of last-coordinate nodes.

For each tuple x in D, the set of bad last-coordinate nodes
whose section is avoided above x must itself be dense in Y's
cone. Otherwise restrict to a deeper cone missing these nodes
and erase x from D, contradicting the minimality of D.

Finiteness here is local finiteness of actual input source levels;
no uniform branching degree, homogeneous alphabet or HL assumption
enters this proof.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- The bad last-coordinate nodes at scale n at which a fixed
level-k front tuple supplies an avoiding matrix. -/
def heterogeneousAvoidWitnessSet
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k n : ℕ) (Y : Set U)
    (x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k) : Set U :=
  {y | y ∈ Y ∧
    HeterogeneousBadSectionAt P Q k n y ∧
    HeterogeneousSectionAvoidAt P Q y x.1 n}

/-- A witness belonging to a minimum avoiding cover remains
cone-dense among bad sections at every density scale. -/
theorem heterogeneousAvoidWitnessSet_coneDense_of_minimal
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {X : Set U}
    (C : HeterogeneousAvoidCover P Q k X)
    (hmin : ∀ C' : HeterogeneousAvoidCover P Q k X,
      C.D.card ≤ C'.D.card)
    {x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k}
    (hxD : x ∈ C.D)
    (n : ℕ) :
    HeterogeneousConeDense (P (Fin.last d))
      (heterogeneousAvoidWitnessSet P Q k n C.Y x)
      C.root := by
  classical
  let N : ℕ := max C.n0 n
  have hmain :
      HeterogeneousConeDense (P (Fin.last d))
        (heterogeneousAvoidWitnessSet P Q k N C.Y x)
        C.root := by
    by_contra hnot
    have hmissing :
        ∃ u : U, u ∈ (P (Fin.last d)).carrier ∧
          C.root ≤ u ∧
          ∀ y ∈ heterogeneousAvoidWitnessSet
            P Q k N C.Y x, ¬ u ≤ y := by
      change ¬ ∀ z ∈ (P (Fin.last d)).carrier,
        C.root ≤ z →
          ∃ y ∈ heterogeneousAvoidWitnessSet
            P Q k N C.Y x, z ≤ y at hnot
      push_neg at hnot
      exact hnot
    obtain ⟨u, huIn, hrootu, huAvoid⟩ := hmissing
    let Y' : Set U := heterogeneousRestrictCone C.Y u
    have hY'dense :
        HeterogeneousConeDense (P (Fin.last d)) Y' u :=
      heterogeneousConeDense_restrict (P (Fin.last d))
        C.Y C.Y_dense hrootu
    let C' : HeterogeneousAvoidCover P Q k X := {
      D := C.D.erase x
      n0 := N
      Y := Y'
      root := u
      root_mem := huIn
      Y_subset := by
        intro y hy
        exact C.Y_subset hy.1
      Y_inside := by
        intro y hy
        exact C.Y_inside hy.1
      Y_dense := hY'dense
      cover := by
        intro m hm y hyY' hbad
        have hmC : C.n0 ≤ m :=
          (Nat.le_max_left C.n0 n).trans hm
        obtain ⟨z, hzD, hzAvoid⟩ :=
          C.cover m hmC y hyY'.1 hbad
        have hzx : z ≠ x := by
          intro heq
          subst z
          have hyWitness :
              y ∈ heterogeneousAvoidWitnessSet
                P Q k N C.Y x := by
            refine ⟨hyY'.1, ?_, ?_⟩
            · exact heterogeneousBadSectionAt_of_le
                P Q k hm y hbad
            · exact heterogeneousSectionAvoidAt_of_le
                P Q y x.1 hm hzAvoid
          exact (huAvoid y hyWitness) hyY'.2
        exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hzD⟩,
          hzAvoid⟩
    }
    have hcard : C'.D.card < C.D.card := by
      change (C.D.erase x).card < C.D.card
      exact Finset.card_erase_lt_of_mem hxD
    exact (not_lt_of_ge (hmin C')) hcard
  have hnN : n ≤ N := Nat.le_max_right _ _
  intro z hz hrootz
  obtain ⟨y, hyWitness, hzy⟩ := hmain z hz hrootz
  refine ⟨y, ?_, hzy⟩
  obtain ⟨hyY, hbadN, hAvoidN⟩ := hyWitness
  exact ⟨hyY,
    heterogeneousBadSectionAt_of_le P Q k hnN y hbadN,
    heterogeneousSectionAvoidAt_of_le P Q y x.1 hnN hAvoidN⟩

/-- Above any later last-coordinate cone, one finds a section
with an avoiding witness for the fixed minimum-cover tuple. -/
theorem exists_heterogeneousAvoidWitness_above_of_minimal
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {X : Set U}
    (C : HeterogeneousAvoidCover P Q k X)
    (hmin : ∀ C' : HeterogeneousAvoidCover P Q k X,
      C.D.card ≤ C'.D.card)
    {x : HeterogeneousLevelTuple
      (fun i : Fin d => P i.castSucc) k}
    (hxD : x ∈ C.D)
    {t : U} (ht : t ∈ (P (Fin.last d)).carrier)
    (hroot : C.root ≤ t)
    (n : ℕ) :
    ∃ y : U, t ≤ y ∧ y ∈ C.Y ∧
      HeterogeneousBadSectionAt P Q k n y ∧
      HeterogeneousSectionAvoidAt P Q y x.1 n := by
  obtain ⟨y, hy, hty⟩ :=
    (heterogeneousAvoidWitnessSet_coneDense_of_minimal
      P Q k C hmin hxD n) t ht hroot
  exact ⟨y, hty, hy.1, hy.2.1, hy.2.2⟩

end GeneralTree
end Milliken
