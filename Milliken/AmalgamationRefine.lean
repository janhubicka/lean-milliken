import Milliken.AmalgamationBoundary
import RamseySpace.Axioms

/-!
# Textbook A.3(2) for the strong-subtree Ramsey space

This completes the amalgamation axiom from Todorčević, Chapter 6.

For a nonempty finite stem `a = r_n(B ∘ H)` of depth `d`, the
depth-boundary splice keeps the first `d` levels of `B` fixed and,
above every boundary node actually used by the stem, follows a rebased cone
of `H`.  Any further reduction with the same `n`-stem is forced by
strongness into one of those used cones, hence its range is contained in
`B ∘ H`.

The empty stem is the trivial depth-zero case.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- The empty approximation has depth zero in every point. -/
theorem depth_zero_of_level_zero
    [Finite ι] [Nonempty ι]
    (a : Approx ι 0) (B : StrongEmbedding ι)
    (hd : (finitization (ι := ι)).HasDepth a B d) :
    d = 0 := by
  let S := approximationSystem ι
  have haB : a = S.approx 0 B := by
    rcases S.approx_surjective 0 a with ⟨X, hX⟩
    rw [← hX, S.approx_zero X, S.approx_zero B]
  have hle0 :
      (finitization (ι := ι)).leFin
        (⟨0, a⟩ : S.FiniteApprox)
        (S.finiteApprox 0 B) := by
    rw [haB]
    exact (finitization (ι := ι)).leFin_refl _
  by_contra hd0
  have hpos : 0 < d := Nat.pos_of_ne_zero hd0
  exact (hd.2 0 hpos) hle0

/-- Textbook A.3(2): if `A ∈ [a,B]` and `d = depth_B(a)`, there is
`A' ∈ [d,B]` with `[a,A'] ⊆ [a,A]`. -/
theorem amalgamation_refine_standard
    [Finite ι] [Nonempty ι]
    {n : ℕ} (a : Approx ι n) (B : StrongEmbedding ι) {d : ℕ}
    (hd : (finitization (ι := ι)).HasDepth a B d)
    {A : StrongEmbedding ι}
    (hA : A ∈ (S ι).neighborhood a B) :
    ∃ A', A' ∈ (S ι).levelNeighborhood d B ∧
      (S ι).neighborhood a A' ⊆ (S ι).neighborhood a A := by
  by_cases hn0 : n = 0
  · subst n
    have hd0 : d = 0 :=
      depth_zero_of_level_zero a B hd
    subst d
    refine ⟨A, ?_, ?_⟩
    · constructor
      · exact hA.1
      · exact (S ι).approx_zero A |>.trans
          ((S ι).approx_zero B).symm
    · exact fun _ h => h
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    rcases hA.1 with ⟨H, hAH⟩
    subst A
    have hnd : n ≤ d := hd.1.1
    have hdpos : 0 < d := hn.trans_le hnd
    have happrox :
        approx ι n (StrongEmbedding.comp B H) = a :=
      hA.2
    have htop :
        ∀ q : LevelNode ι (n - 1),
          (H.toFun q.1).length = d - 1 :=
      factor_top_level_on_depth_pred hn a B H happrox hd
    let J : StrongEmbedding ι :=
      AmalgamationBoundary.splice hn hdpos H htop
    let A' : StrongEmbedding ι :=
      StrongEmbedding.comp B J
    have hA'B :
        A' ∈ (S ι).levelNeighborhood d B := by
      dsimp [A', J]
      exact AmalgamationBoundary.comp_splice_mem_levelNeighborhood
        hn hdpos B H htop
    refine ⟨A', hA'B, ?_⟩
    intro X hX
    rcases hX.1 with ⟨K, hXfac⟩
    subst X
    have hstem :
        approx ι n (StrongEmbedding.comp A' K) =
          approx ι n (StrongEmbedding.comp B H) := by
      exact hX.2.trans happrox.symm
    have hrange :
        StrongEmbedding.range (StrongEmbedding.comp A' K) ⊆
          StrongEmbedding.range (StrongEmbedding.comp B H) := by
      rintro y ⟨s, rfl⟩
      have hJKrange :
          J.toFun (K.toFun s) ∈ StrongEmbedding.range H := by
        by_cases hs : s.length < n
        · have hmap :=
            toFun_eq_of_approx_eq (ι := ι) hstem hs
          change
            B.toFun (J.toFun (K.toFun s)) =
              B.toFun (H.toFun s) at hmap
          have hsource :
              J.toFun (K.toFun s) = H.toFun s :=
            B.injective hmap
          exact ⟨s, hsource.symm⟩
        · have hsge : n ≤ s.length := le_of_not_gt hs
          let r : LevelNode ι n :=
            BoundaryGraft.boundaryPrefix n s hsge
          let q : LevelNode ι (n - 1) :=
            AmalgamationBoundary.parentNode hn r
          have hqlt : q.1.length < n := by
            rw [q.2]
            omega
          have hmapq :=
            toFun_eq_of_approx_eq (ι := ι) hstem hqlt
          change
            B.toFun (J.toFun (K.toFun q.1)) =
              B.toFun (H.toFun q.1) at hmapq
          have hJKeq :
              J.toFun (K.toFun q.1) = H.toFun q.1 :=
            B.injective hmapq
          have hshort :
              (J.toFun (K.toFun q.1)).length < d := by
            rw [hJKeq, htop q]
            omega
          have hJid :
              J.toFun (K.toFun q.1) = K.toFun q.1 := by
            dsimp [J]
            exact BoundaryGraft.graft_toFun_eq_of_length_lt
              (AmalgamationBoundary.spliceFamily hn hdpos H htop)
              (AmalgamationBoundary.spliceFamily_commonLevels
                hn hdpos H htop)
              (K.toFun q.1) hshort
          have hKq :
              K.toFun q.1 = H.toFun q.1 :=
            hJid.symm.trans hJKeq
          have hbranch := K.branch q.1
            (AmalgamationBoundary.lastLabel hn r)
          rw [hKq,
              AmalgamationBoundary.parent_child hn r] at hbranch
          have hfrontK :
              (AmalgamationBoundary.frontierNode
                  hn hdpos H htop r).1.IsPrefix
                (K.toFun r.1) := by
            exact hbranch
          have hrs : r.1.IsPrefix s := by
            dsimp [r, BoundaryGraft.boundaryPrefix]
            exact List.take_prefix n s
          have hfrontKs :
              (AmalgamationBoundary.frontierNode
                  hn hdpos H htop r).1.IsPrefix
                (K.toFun s) :=
            hfrontK.trans (K.prefix_mono hrs)
          dsimp [J]
          exact AmalgamationBoundary.splice_image_mem_range_of_frontier_prefix
            hn hdpos H htop r (K.toFun s) hfrontKs
      rcases hJKrange with ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change
        B.toFun (H.toFun t) =
          B.toFun (J.toFun (K.toFun s))
      rw [ht]
    have hle :
        le ι (StrongEmbedding.comp A' K)
          (StrongEmbedding.comp B H) :=
      (le_iff_range_subset _ _).2 hrange
    exact ⟨hle, hX.2⟩

end StrongTreeSpace
end Milliken
