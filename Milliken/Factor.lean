import Milliken.Finitization

/-!
# Factorization of strong embeddings

For the homogeneous tree, inclusion of the ranges of two strong embeddings
canonically yields a factor strong embedding.  This is the key bridge between
the concrete carrier finitization and the infinite reduction order.

The reflection fields of `StrongEmbedding` make the successor clauses
formal: successor information can be pulled back uniquely through the outer
embedding.
-/

namespace Milliken
namespace StrongTreeSpace

universe u

variable {ι : Type u}

/-- Canonical preimage of a node of `X` in `Y`, assuming
`range X ⊆ range Y`. -/
noncomputable def factorFun (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y) :
    Node ι → Node ι :=
  fun s => Classical.choose (hXY ⟨s, rfl⟩)

theorem factorFun_spec (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    (s : Node ι) :
    Y.toFun (factorFun X Y hXY s) = X.toFun s :=
  Classical.choose_spec (hXY ⟨s, rfl⟩)

theorem factorFun_injective (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y) :
    Function.Injective (factorFun X Y hXY) := by
  intro s t hst
  apply X.injective
  rw [← factorFun_spec X Y hXY s, ← factorFun_spec X Y hXY t, hst]

theorem factorFun_prefix_mono (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    {s t : Node ι} (hst : s.IsPrefix t) :
    (factorFun X Y hXY s).IsPrefix (factorFun X Y hXY t) := by
  apply Y.prefix_reflect
  rw [factorFun_spec X Y hXY s, factorFun_spec X Y hXY t]
  exact X.prefix_mono hst

theorem factorFun_prefix_reflect (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    {s t : Node ι}
    (hst : (factorFun X Y hXY s).IsPrefix (factorFun X Y hXY t)) :
    s.IsPrefix t := by
  apply X.prefix_reflect
  rw [← factorFun_spec X Y hXY s, ← factorFun_spec X Y hXY t]
  exact Y.prefix_mono hst

theorem factorFun_branch (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    (s : Node ι) (i : ι) :
    (child (factorFun X Y hXY s) i).IsPrefix
      (factorFun X Y hXY (child s i)) := by
  apply Y.branch_reflect
  rw [factorFun_spec X Y hXY s, factorFun_spec X Y hXY (child s i)]
  exact X.branch s i

theorem factorFun_branch_reflect (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    (s t : Node ι) (i : ι)
    (h :
      (child (factorFun X Y hXY s) i).IsPrefix
        (factorFun X Y hXY t)) :
    (child s i).IsPrefix t := by
  apply X.branch_reflect s t i
  rw [← factorFun_spec X Y hXY s, ← factorFun_spec X Y hXY t]
  exact (Y.branch (factorFun X Y hXY s) i).trans
    (Y.prefix_mono h)

/-- A canonical source node on each level, used only to name the level map
of the factor embedding. -/
noncomputable def rayNode [Nonempty ι] (n : ℕ) : Node ι :=
  List.replicate n (Classical.choice (inferInstance : Nonempty ι))

@[simp] theorem rayNode_length [Nonempty ι] (n : ℕ) :
    (rayNode (ι := ι) n).length = n := by
  simp [rayNode]

theorem rayNode_prefix [Nonempty ι] {n m : ℕ} (hnm : n ≤ m) :
    (rayNode (ι := ι) n).IsPrefix (rayNode (ι := ι) m) := by
  rcases Nat.exists_eq_add_of_le hnm with ⟨k, rfl⟩
  simp only [rayNode, List.replicate_add]
  exact List.prefix_append _ _

/-- Level map of the factor embedding. -/
noncomputable def factorLevels [Nonempty ι]
    (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    (n : ℕ) : ℕ :=
  (factorFun X Y hXY (rayNode (ι := ι) n)).length

theorem factorFun_same_level [Nonempty ι]
    (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y)
    (s : Node ι) :
    (factorFun X Y hXY s).length =
      factorLevels X Y hXY s.length := by
  rcases X.level_witness with ⟨xlev, hxmono, hxlev⟩
  rcases Y.level_witness with ⟨ylev, hymono, hylev⟩
  have hs := congrArg List.length (factorFun_spec X Y hXY s)
  rw [hylev, hxlev] at hs
  have hr := congrArg List.length
    (factorFun_spec X Y hXY (rayNode (ι := ι) s.length))
  rw [hylev, hxlev] at hr
  simp only [rayNode_length] at hr
  apply hymono.injective
  exact hs.trans hr.symm

theorem factorLevels_strictMono [Nonempty ι]
    (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y) :
    StrictMono (factorLevels X Y hXY) := by
  intro n m hnm
  have hpref : (factorFun X Y hXY (rayNode (ι := ι) n)).IsPrefix
      (factorFun X Y hXY (rayNode (ι := ι) m)) :=
    factorFun_prefix_mono X Y hXY (rayNode_prefix hnm.le)
  have hle := hpref.length_le
  have hne :
      factorFun X Y hXY (rayNode (ι := ι) n) ≠
        factorFun X Y hXY (rayNode (ι := ι) m) := by
    intro heq
    have hnm' := factorFun_injective X Y hXY heq
    have hlen := congrArg List.length hnm'
    simp only [rayNode_length] at hlen
    omega
  have hlt :
      (factorFun X Y hXY (rayNode (ι := ι) n)).length <
        (factorFun X Y hXY (rayNode (ι := ι) m)).length := by
    exact lt_of_le_of_ne hle (by
      intro heq
      apply hne
      exact hpref.eq_of_length heq)
  exact hlt

/-- Inclusion of strong-subtree ranges produces the unique strong factor. -/
noncomputable def factorEmbedding [Nonempty ι]
    (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y) :
    StrongEmbedding ι where
  toFun := factorFun X Y hXY
  injective := factorFun_injective X Y hXY
  prefix_mono := factorFun_prefix_mono X Y hXY
  prefix_reflect := factorFun_prefix_reflect X Y hXY
  branch := factorFun_branch X Y hXY
  branch_reflect := factorFun_branch_reflect X Y hXY
  level_witness := by
    refine ⟨factorLevels X Y hXY, factorLevels_strictMono X Y hXY, ?_⟩
    intro s
    exact factorFun_same_level X Y hXY s

theorem comp_factorEmbedding [Nonempty ι]
    (X Y : StrongEmbedding ι)
    (hXY : StrongEmbedding.range X ⊆ StrongEmbedding.range Y) :
    StrongEmbedding.comp Y (factorEmbedding X Y hXY) = X := by
  apply StrongEmbedding.ext
  intro s
  exact factorFun_spec X Y hXY s

/-- Range inclusion is equivalent to the reduction/factorization order. -/
theorem le_iff_range_subset [Nonempty ι]
    (X Y : StrongEmbedding ι) :
    le ι X Y ↔
      StrongEmbedding.range X ⊆ StrongEmbedding.range Y := by
  constructor
  · rintro ⟨Z, rfl⟩
    rintro x ⟨s, rfl⟩
    exact ⟨Z.toFun s, rfl⟩
  · intro h
    exact ⟨factorEmbedding X Y h, (comp_factorEmbedding X Y h).symm⟩

end StrongTreeSpace
end Milliken
