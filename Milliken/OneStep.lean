import Milliken.GraftRamsey

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
  · subst q
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
        intro hn0
        have : q.1.length = 0 := by simpa [hn0] using q.2
        exact hq (List.length_eq_zero_iff.mp this)
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
  rw [factorSuffix, ← htake]
  exact List.take_append_drop n (H.toFun q.1)

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

end Chapter6
end Milliken
