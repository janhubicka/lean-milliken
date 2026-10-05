import Milliken.BranchEmbedding
import Milliken.HalpernLauchli.StrongSubtreePrep

/-!
# Level-homogeneous fusion from the fixed-base HDHL strengthening

Given a binary coloring and one base vector above which monochromatic level
matrices exist at every density scale, we recursively choose one such matrix
above the previous support level.  Each source node is sent to a point of the
corresponding coordinate set above the literal labelled child of its parent.

The result is a family of strong embeddings with common levels such that each
source level product is monochromatic.  The color is allowed to depend on the
level; the next file extracts an infinite monochromatic subsequence.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- One chosen level-matrix witness, together with the scale at which it is
dense above the fixed base. -/
structure FusionWitness
    {d : ℕ}
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ) where
  scale : ℕ
  base_le_scale : r ≤ scale
  color : Fin 2
  M : Matrix ι d
  level : ℕ
  onLevel : M.OnLevel level
  dense : M.DenseAbove base scale
  monochromatic : ∀ x ∈ M.carrier, c x = color
  scale_le_level : scale ≤ level

/-- A fusion witness exists at every requested scale.  The existential
statement lives in `Prop`; the noncomputable selector below then chooses
one without eliminating a proposition directly into data. -/
theorem exists_fusionWitness
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r q : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hrq : r ≤ q)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    ∃ W : FusionWitness c base r, W.scale = q := by
  rcases hall q with
    ⟨color, M, l, hlevel, hdense, hmono⟩
  let W : FusionWitness c base r := {
    scale := q
    base_le_scale := hrq
    color := color
    M := M
    level := l
    onLevel := hlevel
    dense := hdense
    monochromatic := hmono
    scale_le_level :=
      M.support_ge_of_onLevel_denseAbove
        hd hbase hrq hlevel hdense
  }
  exact ⟨W, rfl⟩

/-- Package one fixed-base monochromatic matrix as a fusion witness. -/
noncomputable def chosenFusionWitness
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r q : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hrq : r ≤ q)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    FusionWitness c base r :=
  Classical.choose
    (exists_fusionWitness hd c base r q hbase hrq hall)

theorem chosenFusionWitness_scale
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r q : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hrq : r ≤ q)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    (chosenFusionWitness hd c base r q hbase hrq hall).scale = q :=
  Classical.choose_spec
    (exists_fusionWitness hd c base r q hbase hrq hall)

/-- The sequence of monochromatic matrices used by the fusion.  The first
matrix is dense one level above the base.  Every later matrix is dense one
level above the support of its predecessor. -/
noncomputable def fusionWitnesses
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    ℕ → FusionWitness c base r
  | 0 =>
      chosenFusionWitness hd c base r (r + 1)
        hbase (by omega) hall
  | n + 1 =>
      let W := fusionWitnesses hd c base r hbase hall n
      chosenFusionWitness hd c base r (W.level + 1)
        hbase
        (W.base_le_scale.trans
          (W.scale_le_level.trans (Nat.le_succ W.level)))
        hall

/-- Common target level of the raw fusion on source level `n`. -/
noncomputable def fusionLevels
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) : ℕ :=
  (fusionWitnesses hd c base r hbase hall n).level

@[simp] theorem fusionWitnesses_zero_scale
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    (fusionWitnesses hd c base r hbase hall 0).scale = r + 1 := by
  unfold fusionWitnesses
  exact chosenFusionWitness_scale
    hd c base r (r + 1) hbase (by omega) hall

@[simp] theorem fusionWitnesses_succ_scale
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) :
    (fusionWitnesses hd c base r hbase hall (n + 1)).scale =
      fusionLevels hd c base r hbase hall n + 1 := by
  unfold fusionWitnesses
  exact chosenFusionWitness_scale
    hd c base r
      ((fusionWitnesses hd c base r hbase hall n).level + 1)
      hbase
      ((fusionWitnesses hd c base r hbase hall n).base_le_scale.trans
        ((fusionWitnesses hd c base r hbase hall n).scale_le_level.trans
          (Nat.le_succ
            (fusionWitnesses hd c base r hbase hall n).level)))
      hall

theorem fusionLevels_lt_succ
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) :
    fusionLevels hd c base r hbase hall n <
      fusionLevels hd c base r hbase hall (n + 1) := by
  let W :=
    fusionWitnesses hd c base r hbase hall (n + 1)
  have h := W.scale_le_level
  rw [fusionWitnesses_succ_scale] at h
  exact Nat.lt_of_succ_le h

theorem fusionLevels_strictMono
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    StrictMono (fusionLevels hd c base r hbase hall) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact fusionLevels_lt_succ hd c base r hbase hall n

/-- Choose a point of a fusion witness above a prescribed node on its density
level. -/
noncomputable def fusionWitnessNode
    {d : ℕ}
    {c : (Fin d → Node ι) → Fin 2}
    {base : Fin d → Node ι}
    {r : ℕ}
    (W : FusionWitness c base r)
    (i : Fin d)
    (t : Node ι)
    (ht : t ∈ coneLevel (base i) W.scale) :
    Node ι :=
  Classical.choose (W.dense i ht)

theorem fusionWitnessNode_mem
    {d : ℕ}
    {c : (Fin d → Node ι) → Fin 2}
    {base : Fin d → Node ι}
    {r : ℕ}
    (W : FusionWitness c base r)
    (i : Fin d)
    (t : Node ι)
    (ht : t ∈ coneLevel (base i) W.scale) :
    fusionWitnessNode W i t ht ∈ W.M.coord i :=
  (Classical.choose_spec (W.dense i ht)).1

theorem fusionWitnessNode_prefix
    {d : ℕ}
    {c : (Fin d → Node ι) → Fin 2}
    {base : Fin d → Node ι}
    {r : ℕ}
    (W : FusionWitness c base r)
    (i : Fin d)
    (t : Node ι)
    (ht : t ∈ coneLevel (base i) W.scale) :
    t.IsPrefix (fusionWitnessNode W i t ht) :=
  (Classical.choose_spec (W.dense i ht)).2

/-- State reached after reading a source word of length `n` in one
coordinate. -/
structure BranchFusionState
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (n : ℕ) where
  node : Node ι
  length_eq :
    node.length = fusionLevels hd c base r hbase hall n
  base_prefix : (base i).IsPrefix node
  stage_mem :
    node ∈ (fusionWitnesses hd c base r hbase hall n).M.coord i

/-- Initial coordinate state, chosen from the first monochromatic matrix. -/
noncomputable def initialBranchFusionState
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) :
    BranchFusionState hd c base r hbase hall i 0 := by
  classical
  let W := fusionWitnesses hd c base r hbase hall 0
  let t : Node ι := extendToLevel (base i) W.scale
  have hri : (base i).length ≤ W.scale := by
    rw [hbase i]
    exact W.base_le_scale
  have ht :
      t ∈ coneLevel (base i) W.scale := by
    refine ⟨?_, ?_⟩
    · dsimp [t]
      exact prefix_extendToLevel _ _
    · dsimp [t]
      exact length_extendToLevel hri
  let y : Node ι := fusionWitnessNode W i t ht
  refine {
    node := y
    length_eq := ?_
    base_prefix := ?_
    stage_mem := ?_
  }
  · dsimp [y, fusionLevels]
    exact W.onLevel i y
      (fusionWitnessNode_mem W i t ht)
  · exact
      (prefix_extendToLevel (base i) W.scale).trans
        (fusionWitnessNode_prefix W i t ht)
  · exact fusionWitnessNode_mem W i t ht

/-- One labelled child step of the coordinate fusion. -/
noncomputable def nextBranchFusionState
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) {n : ℕ}
    (S : BranchFusionState hd c base r hbase hall i n)
    (a : ι) :
    BranchFusionState hd c base r hbase hall i (n + 1) := by
  classical
  let W := fusionWitnesses hd c base r hbase hall (n + 1)
  let t : Node ι := child S.node a
  have htlen : t.length = W.scale := by
    dsimp [t]
    rw [show (child S.node a).length = S.node.length + 1 by
      simp [child]]
    rw [S.length_eq, fusionWitnesses_succ_scale]
  have htpref : (base i).IsPrefix t :=
    S.base_prefix.trans (List.prefix_append _ _)
  have ht :
      t ∈ coneLevel (base i) W.scale :=
    ⟨htpref, htlen⟩
  let y : Node ι := fusionWitnessNode W i t ht
  refine {
    node := y
    length_eq := ?_
    base_prefix := ?_
    stage_mem := ?_
  }
  · dsimp [y, fusionLevels]
    exact W.onLevel i y
      (fusionWitnessNode_mem W i t ht)
  · exact htpref.trans
      (fusionWitnessNode_prefix W i t ht)
  · exact fusionWitnessNode_mem W i t ht

theorem nextBranchFusionState_branch
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) {n : ℕ}
    (S : BranchFusionState hd c base r hbase hall i n)
    (a : ι) :
    (child S.node a).IsPrefix
      (nextBranchFusionState
        hd c base r hbase hall i S a).node := by
  classical
  unfold nextBranchFusionState
  simp only
  exact fusionWitnessNode_prefix _ _ _ _

/-- A sigma-packed state, convenient for folding along a source word. -/
abbrev PackedBranchFusionState
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) :=
  Σ n, BranchFusionState hd c base r hbase hall i n

noncomputable def packedBranchFusionStep
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d)
    (S : PackedBranchFusionState hd c base r hbase hall i)
    (a : ι) :
    PackedBranchFusionState hd c base r hbase hall i :=
  ⟨S.1 + 1,
    nextBranchFusionState
      hd c base r hbase hall i S.2 a⟩

noncomputable def runBranchFusion
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) :
    PackedBranchFusionState hd c base r hbase hall i :=
  List.foldl
    (packedBranchFusionStep
      hd c base r hbase hall i)
    ⟨0, initialBranchFusionState
      hd c base r hbase hall i⟩
    s

theorem foldBranchFusion_index
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d)
    (S : PackedBranchFusionState hd c base r hbase hall i)
    (s : Node ι) :
    (List.foldl
      (packedBranchFusionStep
        hd c base r hbase hall i)
      S s).1 = S.1 + s.length := by
  induction s generalizing S with
  | nil =>
      simp
  | cons a s ih =>
      simp only [List.foldl]
      rw [ih]
      simp [packedBranchFusionStep]
      omega

theorem runBranchFusion_index
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) :
    (runBranchFusion
      hd c base r hbase hall i s).1 = s.length := by
  unfold runBranchFusion
  rw [foldBranchFusion_index]
  simp

/-- Node map produced by the raw fusion. -/
noncomputable def branchFusionNode
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) : Node ι :=
  (runBranchFusion
    hd c base r hbase hall i s).2.node

theorem branchFusionNode_length
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) :
    (branchFusionNode
      hd c base r hbase hall i s).length =
      fusionLevels hd c base r hbase hall s.length := by
  unfold branchFusionNode
  generalize hR :
      runBranchFusion hd c base r hbase hall i s = R
  rcases R with ⟨m, S⟩
  have hidx :=
    runBranchFusion_index
      hd c base r hbase hall i s
  rw [hR] at hidx
  dsimp at hidx
  subst m
  exact S.length_eq

theorem branchFusionNode_stage_mem
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) :
    branchFusionNode hd c base r hbase hall i s ∈
      (fusionWitnesses
        hd c base r hbase hall s.length).M.coord i := by
  unfold branchFusionNode
  generalize hR :
      runBranchFusion hd c base r hbase hall i s = R
  rcases R with ⟨m, S⟩
  have hidx :=
    runBranchFusion_index
      hd c base r hbase hall i s
  rw [hR] at hidx
  dsimp at hidx
  subst m
  exact S.stage_mem

theorem runBranchFusion_child
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) (a : ι) :
    runBranchFusion hd c base r hbase hall i (child s a) =
      packedBranchFusionStep
        hd c base r hbase hall i
        (runBranchFusion hd c base r hbase hall i s) a := by
  simp [runBranchFusion, child, List.foldl_append,
    packedBranchFusionStep]

theorem branchFusionNode_branch
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) (s : Node ι) (a : ι) :
    (child
      (branchFusionNode hd c base r hbase hall i s) a).IsPrefix
      (branchFusionNode
        hd c base r hbase hall i (child s a)) := by
  change
    (child
      (runBranchFusion
        hd c base r hbase hall i s).2.node a).IsPrefix
      (runBranchFusion
        hd c base r hbase hall i (child s a)).2.node
  rw [runBranchFusion_child]
  exact nextBranchFusionState_branch
    hd c base r hbase hall i
      (runBranchFusion
        hd c base r hbase hall i s).2 a

/-- Raw strong embedding in coordinate `i`. -/
noncomputable def branchFusionEmbedding
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (i : Fin d) :
    StrongEmbedding ι :=
  StrongEmbedding.ofBranchLevels
    (branchFusionNode hd c base r hbase hall i)
    (fusionLevels hd c base r hbase hall)
    (fusionLevels_strictMono hd c base r hbase hall)
    (branchFusionNode_length hd c base r hbase hall i)
    (branchFusionNode_branch hd c base r hbase hall i)

/-- The coordinate embeddings have one common level set. -/
theorem branchFusion_commonLevels
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q) :
    HasCommonLevels
      (fun i =>
        branchFusionEmbedding
          hd c base r hbase hall i)
      (fusionLevels hd c base r hbase hall) := by
  refine
    ⟨fusionLevels_strictMono
      hd c base r hbase hall, ?_⟩
  intro i s
  exact branchFusionNode_length
    hd c base r hbase hall i s

/-- Every source level product of the raw fusion is monochromatic, with the
color recorded by that level's witness matrix. -/
theorem branchFusion_level_monochromatic
    [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (c : (Fin d → Node ι) → Fin 2)
    (base : Fin d → Node ι)
    (r : ℕ)
    (hbase : IsLevelVectorAt r base)
    (hall : ∀ q : ℕ, LevelMonochromaticAbove c base q)
    (n : ℕ) (x : Fin d → Node ι)
    (hx : ∀ i, (x i).length = n) :
    c (fun i =>
      (branchFusionEmbedding
        hd c base r hbase hall i).toFun (x i)) =
      (fusionWitnesses
        hd c base r hbase hall n).color := by
  let W := fusionWitnesses hd c base r hbase hall n
  apply W.monochromatic
  intro i
  change
    branchFusionNode hd c base r hbase hall i (x i) ∈
      W.M.coord i
  have hmem :=
    branchFusionNode_stage_mem
      hd c base r hbase hall i (x i)
  simpa [W, hx i] using hmem

end HalpernLauchli
end Milliken
