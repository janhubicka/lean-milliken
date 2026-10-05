import Milliken.Tree

/-!
# Building strong embeddings from branch-preserving maps

Several Chapter 3 fusion arguments naturally construct the node map first:
all nodes on source level `n` are sent to one target level `levels n`, and
the literal `i`-child of the image of `s` lies below the image of the
`i`-child of `s`.

Those two facts already imply injectivity and reflection of both prefixes and
branch labels.  This file packages the elementary list argument once, so the
Halpern--Läuchli fusion code only has to establish the constructive clauses.
-/

namespace Milliken
namespace StrongEmbedding

universe u
variable {ι : Type u}

/-- Immediate branch preservation implies monotonicity for arbitrary
prefixes. -/
theorem prefix_mono_of_branch
    (f : Node ι → Node ι)
    (hbranch :
      ∀ (s : Node ι) (i : ι),
        (child (f s) i).IsPrefix (f (child s i))) :
    ∀ {s t : Node ι}, s.IsPrefix t → (f s).IsPrefix (f t) := by
  intro s t hst
  rcases hst with ⟨u, rfl⟩
  induction u generalizing s with
  | nil =>
      simp
  | cons a u ih =>
      have h₀ :
          (f s).IsPrefix (child (f s) a) := by
        exact List.prefix_append _ _
      have h₁ := hbranch s a
      have h₂ := ih (s := child s a)
      simpa [child, List.append_assoc] using
        h₀.trans (h₁.trans h₂)

/-- Auxiliary prefix reflection above a common source prefix. -/
theorem prefix_reflect_aux
    (f : Node ι → Node ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hsame : ∀ s : Node ι, (f s).length = levels s.length)
    (hbranch :
      ∀ (s : Node ι) (i : ι),
        (child (f s) i).IsPrefix (f (child s i)))
    (p u v : Node ι)
    (h :
      (f (p ++ u)).IsPrefix (f (p ++ v))) :
    u.IsPrefix v := by
  let hmono :
      ∀ {s t : Node ι}, s.IsPrefix t → (f s).IsPrefix (f t) :=
    prefix_mono_of_branch f hbranch
  induction u generalizing p v with
  | nil =>
      exact List.nil_prefix
  | cons a u ih =>
      cases v with
      | nil =>
          have hlen := h.length_le
          rw [hsame, hsame] at hlen
          have hsrc :
              (p ++ a :: u).length > p.length := by
            simp
          have hlev :
              levels p.length <
                levels (p ++ a :: u).length :=
            hlevels hsrc
          simp only [List.append_nil] at hlen
          exact ((not_lt_of_ge hlen) hlev).elim
      | cons b v =>
          have hpa :
              (child p a).IsPrefix (p ++ a :: u) := by
            simpa [child, List.append_assoc] using
              (List.prefix_append (p ++ [a]) u)
          have hpb :
              (child p b).IsPrefix (p ++ b :: v) := by
            simpa [child, List.append_assoc] using
              (List.prefix_append (p ++ [b]) v)
          have ha :
              (child (f p) a).IsPrefix
                (f (p ++ a :: u)) :=
            (hbranch p a).trans (hmono hpa)
          have hb :
              (child (f p) b).IsPrefix
                (f (p ++ b :: v)) :=
            (hbranch p b).trans (hmono hpb)
          have ha' :
              (child (f p) a).IsPrefix
                (f (p ++ b :: v)) :=
            ha.trans h
          have hae :=
            List.prefix_iff_eq_take.mp ha'
          have hbe :=
            List.prefix_iff_eq_take.mp hb
          have hmark :
              child (f p) a = child (f p) b := by
            calc
              child (f p) a =
                  (f (p ++ b :: v)).take
                    (child (f p) a).length := hae
              _ =
                  (f (p ++ b :: v)).take
                    (child (f p) b).length := by
                    simp [child]
              _ = child (f p) b := hbe.symm
          have hab : a = b := by
            have hs :
                ([a] : List ι) = [b] := by
              exact List.append_cancel_left hmark
            simpa using hs
          subst b
          have huv :
              u.IsPrefix v := by
            apply ih (p := child p a)
            simpa [child, List.append_assoc] using h
          rcases huv with ⟨w, rfl⟩
          exact ⟨w, by simp⟩

/-- Branch preservation plus a common strictly increasing level map reflects
all prefixes. -/
theorem prefix_reflect_of_branch
    (f : Node ι → Node ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hsame : ∀ s : Node ι, (f s).length = levels s.length)
    (hbranch :
      ∀ (s : Node ι) (i : ι),
        (child (f s) i).IsPrefix (f (child s i))) :
    ∀ {s t : Node ι}, (f s).IsPrefix (f t) → s.IsPrefix t := by
  intro s t h
  have h' :
      (f ([] ++ s)).IsPrefix (f ([] ++ t)) := by
    simpa using h
  simpa using
    (prefix_reflect_aux f levels hlevels hsame hbranch [] s t h')

/-- The same hypotheses reflect the labelled immediate branch relation. -/
theorem branch_reflect_of_branch
    (f : Node ι → Node ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hsame : ∀ s : Node ι, (f s).length = levels s.length)
    (hbranch :
      ∀ (s : Node ι) (i : ι),
        (child (f s) i).IsPrefix (f (child s i))) :
    ∀ (s t : Node ι) (i : ι),
      (child (f s) i).IsPrefix (f t) →
        (child s i).IsPrefix t := by
  let hmono :
      ∀ {s t : Node ι}, s.IsPrefix t → (f s).IsPrefix (f t) :=
    prefix_mono_of_branch f hbranch
  let hreflect :
      ∀ {s t : Node ι}, (f s).IsPrefix (f t) → s.IsPrefix t :=
    prefix_reflect_of_branch f levels hlevels hsame hbranch
  intro s t i h
  have hst : s.IsPrefix t := by
    apply hreflect
    exact (List.prefix_append (f s) [i]).trans h
  rcases hst with ⟨u, rfl⟩
  cases u with
  | nil =>
      have hlen := h.length_le
      simp [child, hsame] at hlen
  | cons j u =>
      have hp :
          (child s j).IsPrefix (s ++ j :: u) := by
        simpa [child, List.append_assoc] using
          (List.prefix_append (s ++ [j]) u)
      have hj :
          (child (f s) j).IsPrefix
            (f (s ++ j :: u)) :=
        (hbranch s j).trans (hmono hp)
      have hie :=
        List.prefix_iff_eq_take.mp h
      have hje :=
        List.prefix_iff_eq_take.mp hj
      have hmark :
          child (f s) i = child (f s) j := by
        calc
          child (f s) i =
              (f (s ++ j :: u)).take
                (child (f s) i).length := hie
          _ =
              (f (s ++ j :: u)).take
                (child (f s) j).length := by
                simp [child]
          _ = child (f s) j := hje.symm
      have hij : i = j := by
        have hs :
            ([i] : List ι) = [j] := by
          exact List.append_cancel_left hmark
        simpa using hs
      subst j
      simpa [child, List.append_assoc] using
        (List.prefix_append (s ++ [i]) u)

/-- Package the constructive level and branch clauses as a strong embedding. -/
noncomputable def ofBranchLevels
    (f : Node ι → Node ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hsame : ∀ s : Node ι, (f s).length = levels s.length)
    (hbranch :
      ∀ (s : Node ι) (i : ι),
        (child (f s) i).IsPrefix (f (child s i))) :
    StrongEmbedding ι := by
  let hmono :
      ∀ {s t : Node ι}, s.IsPrefix t → (f s).IsPrefix (f t) :=
    prefix_mono_of_branch f hbranch
  let hreflect :
      ∀ {s t : Node ι}, (f s).IsPrefix (f t) → s.IsPrefix t :=
    prefix_reflect_of_branch f levels hlevels hsame hbranch
  exact {
    toFun := f
    injective := by
      intro s t hst
      have h₁ : s.IsPrefix t := by
        apply hreflect
        simpa [hst]
      have h₂ : t.IsPrefix s := by
        apply hreflect
        simpa [hst]
      exact h₁.eq_of_length
        (le_antisymm h₁.length_le h₂.length_le)
    prefix_mono := hmono
    prefix_reflect := hreflect
    branch := hbranch
    branch_reflect :=
      branch_reflect_of_branch
        f levels hlevels hsame hbranch
    level_witness := ⟨levels, hlevels, hsame⟩
  }

end StrongEmbedding
end Milliken
