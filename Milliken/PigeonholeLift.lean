import Milliken.Pigeonhole
import Milliken.Amalgamation
import Milliken.FinitizationOrder
import RamseySpace.Axioms

/-!
# Lifting the canonical pigeonhole lemma to A.4

The Halpern--Läuchli argument naturally homogenizes one-step extensions of
the canonical stem `r_n(T)`.  Todorčević's full A.4 has an arbitrary finite
approximation `a` of depth `d` in `B`.

The passage is purely axiomatic: A.3(1) first produces some `T ∈ [a,B]`;
the canonical lemma gives a homogeneous `S ∈ [n,T]`; textbook A.3(2)
then refines `S` to `A ∈ [d,B]` with `[a,A] ⊆ [a,S]`.  Hence every
one-step extension below `A` is already one below `S`.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

abbrev TreeSystem (ι : Type u) :=
  StrongTreeSpace.approximationSystem ι

/-- Lift the canonical-stem pigeonhole lemma through textbook A.3(2). -/
theorem pigeonhole_of_canonical_and_refine
    [Finite ι] [Nonempty ι]
    (hCanonical :
      ∀ {n : ℕ} (T : StrongEmbedding ι)
        (O : Set (StrongTreeSpace.Approx ι (n + 1))),
        ∃ S : StrongEmbedding ι,
          S ∈ (TreeSystem ι).levelNeighborhood n T ∧
            ((TreeSystem ι).oneStepApproximations
                  (StrongTreeSpace.approx ι n T) S ⊆ O ∨
              Disjoint
                ((TreeSystem ι).oneStepApproximations
                  (StrongTreeSpace.approx ι n T) S)
                O))
    (hRefine :
      ∀ {n : ℕ} (a : (TreeSystem ι).Approx n)
        (B : (TreeSystem ι).Point) {d : ℕ},
        (StrongTreeSpace.finitization (ι := ι)).HasDepth a B d →
        ∀ {A : (TreeSystem ι).Point},
          A ∈ (TreeSystem ι).neighborhood a B →
          ∃ A', A' ∈ (TreeSystem ι).levelNeighborhood d B ∧
            (TreeSystem ι).neighborhood a A' ⊆
              (TreeSystem ι).neighborhood a A)
    {n : ℕ} (a : (TreeSystem ι).Approx n)
    (B : (TreeSystem ι).Point) {d : ℕ}
    (hd : (StrongTreeSpace.finitization (ι := ι)).HasDepth a B d)
    (O : Set ((TreeSystem ι).Approx (n + 1))) :
    ∃ A, A ∈ (TreeSystem ι).levelNeighborhood d B ∧
      ((TreeSystem ι).oneStepApproximations a A ⊆ O ∨
        Disjoint ((TreeSystem ι).oneStepApproximations a A) O) := by
  let S := TreeSystem ι
  have hBlevel : B ∈ S.levelNeighborhood d B :=
    S.self_mem_levelNeighborhood d B
  rcases StrongTreeSpace.amalgamation_nonempty a B hd hBlevel with
    ⟨T, hTB, hTa⟩
  have hT : T ∈ S.neighborhood a B :=
    ⟨hTB, hTa⟩
  have hCanonicalO :
      Set (StrongTreeSpace.Approx ι (n + 1)) := by
    exact O
  rcases hCanonical T hCanonicalO with
    ⟨U, hUT, hUhom⟩
  have hUa : S.approx n U = a := by
    exact hUT.2.trans hT.2
  have hUB : S.le U B :=
    S.le_trans hUT.1 hT.1
  have hUneigh : U ∈ S.neighborhood a B :=
    ⟨hUB, hUa⟩
  have hTaConcrete :
      StrongTreeSpace.approx ι n T = a := by
    exact hT.2
  have hOeq : hCanonicalO = O := rfl
  have hUhom' :
      S.oneStepApproximations a U ⊆ O ∨
        Disjoint (S.oneStepApproximations a U) O := by
    have h := hUhom
    rw [hTaConcrete, hOeq] at h
    exact h
  rcases hRefine a B hd hUneigh with
    ⟨A, hAB, hsub⟩
  have hone :
      S.oneStepApproximations a A ⊆
        S.oneStepApproximations a U := by
    intro b hb
    rcases hb with ⟨X, hXA, hXb⟩
    exact ⟨X, hsub hXA, hXb⟩
  refine ⟨A, hAB, ?_⟩
  rcases hUhom' with hO | hdis
  · exact Or.inl (hone.trans hO)
  · right
    apply Set.disjoint_left.2
    intro b hbA hbO
    exact (Set.disjoint_left.1 hdis) (hone hbA) hbO

/-- Full A.4 follows from strong-subtree Halpern--Läuchli once textbook
A.3(2) is available. -/
theorem pigeonhole_of_strongSubtreeHL_and_refine
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι)
    (hRefine :
      ∀ {n : ℕ} (a : (TreeSystem ι).Approx n)
        (B : (TreeSystem ι).Point) {d : ℕ},
        (StrongTreeSpace.finitization (ι := ι)).HasDepth a B d →
        ∀ {A : (TreeSystem ι).Point},
          A ∈ (TreeSystem ι).neighborhood a B →
          ∃ A', A' ∈ (TreeSystem ι).levelNeighborhood d B ∧
            (TreeSystem ι).neighborhood a A' ⊆
              (TreeSystem ι).neighborhood a A) :
    ∀ {n : ℕ} (a : (TreeSystem ι).Approx n)
      (B : (TreeSystem ι).Point) {d : ℕ},
      (StrongTreeSpace.finitization (ι := ι)).HasDepth a B d →
      ∀ O : Set ((TreeSystem ι).Approx (n + 1)),
        ∃ A, A ∈ (TreeSystem ι).levelNeighborhood d B ∧
          ((TreeSystem ι).oneStepApproximations a A ⊆ O ∨
            Disjoint ((TreeSystem ι).oneStepApproximations a A) O) := by
  exact pigeonhole_of_canonical_and_refine
    (canonicalPigeonhole_of_strongSubtreeHL hHL) hRefine

end Chapter6
end Milliken
