import Milliken.Chapter6

/-!
# Factors which preserve a finite strong stem

A reduction `S ∘ H` has the same `n`th approximation as `S` precisely
when the factor `H` fixes all source nodes below level `n`.  On the
boundary level, strongness then forces `H(q)` to extend `q`.

These elementary source-tree facts are the converse half of the tuple
encoding used in the proof of Todorčević's Lemma 6.1.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

/-- Equality of the first `n` approximations forces the right factor to fix
every source node below level `n`. -/
theorem factor_fixes_below {n : ℕ}
    (S H : StrongEmbedding ι)
    (happrox :
      StrongTreeSpace.approx ι n (StrongEmbedding.comp S H) =
        StrongTreeSpace.approx ι n S)
    {s : Node ι} (hs : s.length < n) :
    H.toFun s = s := by
  let sn : StrongTreeSpace.FiniteNode ι n := ⟨s, hs⟩
  have h := congrArg
    (fun a : StrongTreeSpace.Approx ι n => a.1 sn) happrox
  change S.toFun (H.toFun s) = S.toFun s at h
  exact S.injective h

/-- If a strong factor fixes all lower levels, every boundary node is a
prefix of its image. -/
theorem boundary_prefix_factor {n : ℕ}
    (H : StrongEmbedding ι)
    (hfix : ∀ (s : Node ι), s.length < n → H.toFun s = s)
    (q : LevelNode ι n) :
    q.1.IsPrefix (H.toFun q.1) := by
  by_cases hq : q.1 = []
  · rw [hq]
    exact List.nil_prefix _
  · let p : Node ι := q.1.dropLast
    let i : ι := q.1.getLast hq
    have hqeq : p ++ [i] = q.1 := by
      dsimp [p, i]
      exact List.dropLast_append_getLast hq
    have hplen : p.length < n := by
      dsimp [p]
      rw [List.length_dropLast, q.2]
      have hn : 0 < n := by
        by_contra hnpos
        have hn0 : n = 0 := Nat.eq_zero_of_not_pos hnpos
        have hlen0 : q.1.length = 0 := by
          simpa [hn0] using q.2
        exact hq (List.length_eq_zero_iff.mp hlen0)
      omega
    have hpfix : H.toFun p = p := hfix p hplen
    have hb := H.branch p i
    rw [hpfix] at hb
    simpa [child, hqeq] using hb

/-- Suffix selected by a factor above a boundary node. -/
def factorSuffix {n : ℕ}
    (H : StrongEmbedding ι) (q : LevelNode ι n) : Node ι :=
  (H.toFun q.1).drop n

/-- A boundary node followed by its factor suffix reconstructs its image. -/
theorem boundary_append_factorSuffix {n : ℕ}
    (H : StrongEmbedding ι)
    (hfix : ∀ (s : Node ι), s.length < n → H.toFun s = s)
    (q : LevelNode ι n) :
    q.1 ++ factorSuffix H q = H.toFun q.1 := by
  have hpref := boundary_prefix_factor H hfix q
  have htake :
      (H.toFun q.1).take n = q.1 := by
    have h := List.prefix_iff_eq_take.mp hpref
    rw [q.2] at h
    exact h.symm
  calc
    q.1 ++ factorSuffix H q
        = (H.toFun q.1).take n ++ (H.toFun q.1).drop n := by
            rw [factorSuffix, htake]
    _ = H.toFun q.1 := List.take_append_drop n (H.toFun q.1)

/-- Evaluation of a boundary graft on a boundary node followed by a
source suffix. -/
theorem graft_boundary_append [Nonempty ι] {n : ℕ}
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : BoundaryGraft.HasCommonLevels F)
    (q : LevelNode ι n) (r : Node ι) :
    (BoundaryGraft.graft F hF).toFun (q.1 ++ r) =
      q.1 ++ (F q).toFun r := by
  change BoundaryGraft.graftFun F (q.1 ++ r) =
    q.1 ++ (F q).toFun r
  have hge : n ≤ (q.1 ++ r).length := by
    simp [q.2]
  rw [BoundaryGraft.graftFun_of_ge F (q.1 ++ r) hge]
  have hb :
      BoundaryGraft.boundaryPrefix n (q.1 ++ r) hge = q := by
    apply Subtype.ext
    dsimp [BoundaryGraft.boundaryPrefix]
    have hnq : n ≤ q.1.length := by
      rw [q.2]
    rw [List.take_append_of_le_length hnq]
    apply (List.take_eq_self_iff _).2
    rw [q.2]
  have hd : (q.1 ++ r).drop n = r := by
    have hdrop :=
      List.drop_append_of_le_length (l₂ := r)
        (show n ≤ q.1.length by rw [q.2])
    simpa [q.2] using hdrop
  rw [hb, hd]

/-- Factor suffixes of all nodes on one boundary level have one common
length. -/
theorem factorSuffix_commonLevel {n : ℕ}
    (H : StrongEmbedding ι) :
    ∃ m : ℕ, ∀ q : LevelNode ι n,
      (factorSuffix H q).length = m := by
  rcases H.level_witness with ⟨levels, hmono, hlevels⟩
  refine ⟨levels n - n, ?_⟩
  intro q
  simp [factorSuffix, List.length_drop, hlevels, q.2]


/-- Converse to the tuple construction.  Any reduction of a boundary graft
which preserves the old `n`-stem has its new level described by one
common-level tuple inside the chosen boundary subtrees. -/
theorem factor_oneStep_eq_tuple [Nonempty ι] {n : ℕ}
    (T : StrongEmbedding ι)
    (F : LevelNode ι n → StrongEmbedding ι)
    (hF : BoundaryGraft.HasCommonLevels F)
    (H : StrongEmbedding ι)
    (hstem :
      StrongTreeSpace.approx ι n
          (StrongEmbedding.comp
            (StrongEmbedding.comp T (BoundaryGraft.graft F hF)) H) =
        StrongTreeSpace.approx ι n T) :
    ∃ k : ℕ, ∃ r : LevelNode ι n → Node ι,
      ∃ hr : ∀ q, (r q).length = k,
        ∃ m : ℕ,
          ∃ hx : ∀ q, ((F q).toFun (r q)).length = m,
            StrongTreeSpace.approx ι (n + 1)
                (StrongEmbedding.comp
                  (StrongEmbedding.comp T (BoundaryGraft.graft F hF)) H) =
              tupleApprox T (fun q => (F q).toFun (r q)) hx := by
  let G : StrongEmbedding ι := BoundaryGraft.graft F hF
  let S : StrongEmbedding ι := StrongEmbedding.comp T G
  have hS :
      StrongTreeSpace.approx ι n S =
        StrongTreeSpace.approx ι n T := by
    dsimp [S, G]
    exact BoundaryGraft.approx_comp_graft T F hF
  have hfactor :
      StrongTreeSpace.approx ι n (StrongEmbedding.comp S H) =
        StrongTreeSpace.approx ι n S := by
    calc
      StrongTreeSpace.approx ι n (StrongEmbedding.comp S H)
          = StrongTreeSpace.approx ι n T := by
              simpa [S, G] using hstem
      _ = StrongTreeSpace.approx ι n S := hS.symm
  have hfix :
      ∀ (s : Node ι), s.length < n → H.toFun s = s := by
    intro s hs
    exact factor_fixes_below S H hfactor hs
  rcases factorSuffix_commonLevel (n := n) H with ⟨k, hk⟩
  let levels : ℕ → ℕ := Classical.choose hF
  have hlevels :
      StrictMono levels ∧
        ∀ q s, ((F q).toFun s).length = levels s.length :=
    Classical.choose_spec hF
  let r : LevelNode ι n → Node ι :=
    fun q => factorSuffix H q
  have hr : ∀ q, (r q).length = k := by
    intro q
    exact hk q
  let x : LevelNode ι n → Node ι :=
    fun q => (F q).toFun (r q)
  have hx : ∀ q, (x q).length = levels k := by
    intro q
    dsimp [x]
    rw [hlevels.2 q (r q), hr q]
  refine ⟨k, r, hr, levels k, hx, ?_⟩
  apply Subtype.ext
  funext s
  change
    T.toFun (G.toFun (H.toFun s.1)) =
      T.toFun ((tupleGraft x hx).toFun s.1)
  by_cases hs : s.1.length < n
  · rw [hfix s.1 hs]
    have hG :
        G.toFun s.1 = s.1 := by
      dsimp [G]
      exact BoundaryGraft.graft_toFun_of_lt F hF s.1 hs
    have htuple :
        (tupleGraft x hx).toFun s.1 = s.1 := by
      exact BoundaryGraft.graft_toFun_of_lt
        (tupleCones x) (tupleCones_commonLevels x hx) s.1 hs
    rw [hG, htuple]
  · have hsn : s.1.length = n := by
      have hslt : s.1.length < n + 1 := s.2
      omega
    let q : LevelNode ι n := ⟨s.1, hsn⟩
    have hH :
        H.toFun q.1 = q.1 ++ factorSuffix H q :=
      (boundary_append_factorSuffix H hfix q).symm
    have hG :
        G.toFun (H.toFun q.1) =
          q.1 ++ (F q).toFun (r q) := by
      rw [hH]
      dsimp [G]
      exact graft_boundary_append F hF q (r q)
    have htuple :
        (tupleGraft x hx).toFun q.1 = q.1 ++ x q := by
      have h := graft_boundary_append
        (tupleCones x) (tupleCones_commonLevels x hx) q []
      simpa [tupleGraft, tupleCones] using h
    change
      T.toFun (G.toFun (H.toFun q.1)) =
        T.toFun ((tupleGraft x hx).toFun q.1)
    rw [hG, htuple]

end Chapter6
end Milliken
