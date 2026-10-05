import Milliken.HalpernLauchli.StabilizationGraft
import Milliken.HalpernLauchli.BinaryStrongSubtree

/-!
# One boundary-cone stabilization step

This is the local operation used in the fusion preceding Lemma 3.15.
For one level vector `x` and one binary section `A`, apply binary
strong-subtree Halpern--Läuchli to the product of the cones above `x`.
The selected subtree is grafted into the boundary cone `x`; every other
boundary cone is thinned by the same level selector.  Thus all coordinates
retain a common level set.

The resulting pullback of `A` is constant on the whole product cone above
`x`.  We also record that the graft preserves every source boundary prefix,
which is what makes successive local stabilization steps compatible.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Coordinatewise action of a family of strong embeddings. -/
def mapTuple {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (x : Fin d → Node ι) :
    Fin d → Node ι :=
  fun i => (F i).toFun (x i)

/-- Pull a subset of a product back through a coordinatewise family. -/
def pullbackProduct {d : ℕ}
    (F : Fin d → StrongEmbedding ι)
    (A : Set (Fin d → Node ι)) :
    Set (Fin d → Node ι) :=
  {x | mapTuple F x ∈ A}

/-- A product set is constant on all common-level tuples extending one fixed
boundary vector. -/
def ConstantAbove {d n : ℕ}
    (A : Set (Fin d → Node ι))
    (x : LevelVector ι d n) : Prop :=
  ∀ l : ℕ, ∀ z : Fin d → Node ι,
    IsLevelVectorAt l z →
    (∀ i, (x.1 i).IsPrefix (z i)) →
      (z ∈ A ↔ x.1 ∈ A)

/-- A coordinatewise refinement preserves source prefixes of length `n`. -/
def PreservesBoundary {d : ℕ}
    (n : ℕ) (F : Fin d → StrongEmbedding ι) : Prop :=
  ∀ i s, n ≤ s.length →
    ((F i).toFun s).take n = s.take n

/-- A refinement literally fixes every node below a prescribed boundary. -/
def FixesBelow {d : ℕ}
    (n : ℕ) (F : Fin d → StrongEmbedding ι) : Prop :=
  ∀ i s, s.length < n → (F i).toFun s = s

theorem mapTuple_level
    {d l : ℕ}
    {F : Fin d → StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hF : HasCommonLevels F levels)
    {x : Fin d → Node ι}
    (hx : IsLevelVectorAt l x) :
    IsLevelVectorAt (levels l) (mapTuple F x) := by
  intro i
  dsimp [mapTuple]
  rw [hF.2 i, hx i]

/-- Boundary grafts preserve their source boundary prefix. -/
theorem boundaryGraft_preservesBoundary
    [Nonempty ι]
    {d n : ℕ}
    (F : Fin d → LevelNode ι n → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (hF :
      ∀ i b s, ((F i b).toFun s).length = levels s.length) :
    PreservesBoundary n
      (fun i =>
        BoundaryGraft.graft (F i)
          ⟨levels, hlevels, fun b s => hF i b s⟩) := by
  intro i s hs
  change
    (BoundaryGraft.graftFun (F i) s).take n =
      s.take n
  rw [BoundaryGraft.graftFun_of_ge (F i) s hs]
  have hlen :
      n ≤
        (BoundaryGraft.boundaryPrefix n s hs).1.length := by
    rw [(BoundaryGraft.boundaryPrefix n s hs).2]
  rw [List.take_append_of_le_length hlen]
  change
    (BoundaryGraft.boundaryPrefix n s hs).1 =
      s.take n
  rfl

/-- A boundary-preserving common-level refinement preserves any cone
constancy property already established at that boundary. -/
theorem constantAbove_pullback
    [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    {A : Set (Fin d → Node ι)}
    {x : LevelVector ι d n}
    {F : Fin d → StrongEmbedding ι}
    {levels : ℕ → ℕ}
    (hconst : ConstantAbove A x)
    (hF : HasCommonLevels F levels)
    (hboundary : PreservesBoundary n F) :
    ConstantAbove (pullbackProduct F A) x := by
  intro l z hzlevel hxz
  let Fz : Fin d → Node ι := mapTuple F z
  let Fx : Fin d → Node ι := mapTuple F x.1
  have hFzLevel :
      IsLevelVectorAt (levels l) Fz := by
    dsimp [Fz]
    exact mapTuple_level hF hzlevel
  have hFxLevel :
      IsLevelVectorAt (levels n) Fx := by
    dsimp [Fx]
    exact mapTuple_level hF x.2
  have hprefixZ :
      ∀ i, (x.1 i).IsPrefix (Fz i) := by
    intro i
    have hnl : n ≤ l := by
      let i0 : Fin d := ⟨0, hd⟩
      have hp := hxz i0
      have hlen := hp.length_le
      rw [x.2 i0, hzlevel i0] at hlen
      exact hlen
    have htake :
        (Fz i).take n = x.1 i := by
      dsimp [Fz]
      rw [hboundary i (z i) (by simpa [hzlevel i] using hnl)]
      have hp := hxz i
      have heq := List.prefix_iff_eq_take.mp hp
      rw [x.2 i] at heq
      exact heq.symm
    rw [← htake]
    exact List.take_prefix n (Fz i)
  have hprefixX :
      ∀ i, (x.1 i).IsPrefix (Fx i) := by
    intro i
    have htake :
        (Fx i).take n = x.1 i := by
      dsimp [Fx]
      rw [hboundary i (x.1 i) (by rw [x.2 i])]
      rw [List.take_eq_self_iff]
      exact le_rfl
    rw [← htake]
    exact List.take_prefix n (Fx i)
  have hz := hconst (levels l) Fz hFzLevel hprefixZ
  have hx := hconst (levels n) Fx hFxLevel hprefixX
  change (Fz ∈ A ↔ Fx ∈ A)
  exact hz.trans hx.symm

/-- Boundary family used for one local stabilization step.  On the selected
boundary node use the Halpern--Läuchli subtree; elsewhere use the canonical
selector with the same relative levels. -/
noncomputable def stabilizationBoundaryFamily
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hlevels : StrictMono levels)
    (i : Fin d)
    (b : LevelNode ι n) :
    StrongEmbedding ι :=
  if h : b = ⟨x.1 i, x.2 i⟩ then
    H i
  else
    levelSelector levels hlevels

theorem stabilizationBoundaryFamily_levels
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels)
    (i : Fin d) (b : LevelNode ι n) (s : Node ι) :
    ((stabilizationBoundaryFamily
      x H levels hH.1 i b).toFun s).length =
      levels s.length := by
  classical
  unfold stabilizationBoundaryFamily
  split
  · subst b
    exact hH.2 i s
  · exact levelSelector_toFun_length levels hH.1 s

/-- The coordinate refinements for one local stabilization step. -/
noncomputable def stabilizationGraft
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels)
    (i : Fin d) :
    StrongEmbedding ι :=
  BoundaryGraft.graft
    (stabilizationBoundaryFamily x H levels hH.1 i)
    ⟨levels, hH.1,
      stabilizationBoundaryFamily_levels
        x H levels hH i⟩

theorem stabilizationGraft_commonLevels
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels) :
    HasCommonLevels
      (stabilizationGraft x H levels hH)
      (graftLevelMap n levels) := by
  unfold stabilizationGraft
  exact boundaryGrafts_commonLevels
    (fun i =>
      stabilizationBoundaryFamily x H levels hH.1 i)
    levels hH.1
    (stabilizationBoundaryFamily_levels
      x H levels hH)

theorem stabilizationGraft_preservesBoundary
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels) :
    PreservesBoundary n
      (stabilizationGraft x H levels hH) := by
  unfold stabilizationGraft
  exact boundaryGraft_preservesBoundary
    (fun i =>
      stabilizationBoundaryFamily x H levels hH.1 i)
    levels hH.1
    (stabilizationBoundaryFamily_levels
      x H levels hH)

theorem stabilizationGraft_fixesBelow
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels) :
    FixesBelow n
      (stabilizationGraft x H levels hH) := by
  intro i s hs
  unfold stabilizationGraft
  exact BoundaryGraft.graft_toFun_of_lt
    (stabilizationBoundaryFamily
      x H levels hH.1 i)
    ⟨levels, hH.1,
      stabilizationBoundaryFamily_levels
        x H levels hH i⟩
    s hs

/-- On the selected boundary cone, the stabilization graft is exactly the
Halpern--Läuchli refinement prefixed by that boundary node. -/
theorem stabilizationGraft_toFun_of_prefix
    [Nonempty ι]
    {d n : ℕ}
    (x : LevelVector ι d n)
    (H : Fin d → StrongEmbedding ι)
    (levels : ℕ → ℕ)
    (hH : HasCommonLevels H levels)
    (i : Fin d) (s : Node ι)
    (hxs : (x.1 i).IsPrefix s) :
    (stabilizationGraft x H levels hH i).toFun s =
      x.1 i ++ (H i).toFun (s.drop n) := by
  classical
  have hsge : n ≤ s.length := by
    have hlen := hxs.length_le
    rw [x.2 i] at hlen
    exact hlen
  change
    BoundaryGraft.graftFun
      (stabilizationBoundaryFamily
        x H levels hH.1 i) s =
      x.1 i ++ (H i).toFun (s.drop n)
  rw [BoundaryGraft.graftFun_of_ge
    (stabilizationBoundaryFamily
      x H levels hH.1 i) s hsge]
  have hb :
      BoundaryGraft.boundaryPrefix n s hsge =
        (⟨x.1 i, x.2 i⟩ : LevelNode ι n) := by
    exact BoundaryGraft.boundaryPrefix_eq_of_prefix
      hxs (by rw [x.2 i])
  rw [hb]
  simp [stabilizationBoundaryFamily]

/-- One local fusion step makes the pullback of a product set constant above
the selected boundary vector. -/
theorem exists_stabilizationGraft
    [Finite ι] [Nonempty ι]
    {d n : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (A : Set (Fin d → Node ι))
    (x : LevelVector ι d n) :
    ∃ levels : ℕ → ℕ,
      ∃ F : Fin d → StrongEmbedding ι,
        HasCommonLevels F levels ∧
        PreservesBoundary n F ∧
        FixesBelow n F ∧
        ConstantAbove (pullbackProduct F A) x := by
  classical
  let c : (Fin d → Node ι) → Fin 2 :=
    fun z =>
      if (fun i => x.1 i ++ z i) ∈ A then 1 else 0
  rcases binaryStrongSubtree_of_hdhl hd hHDHL c with
    ⟨color, levels, H, hH, hmono⟩
  let F : Fin d → StrongEmbedding ι :=
    stabilizationGraft x H levels hH
  have hFcommon :
      HasCommonLevels F (graftLevelMap n levels) := by
    dsimp [F]
    exact stabilizationGraft_commonLevels
      x H levels hH
  have hFboundary :
      PreservesBoundary n F := by
    dsimp [F]
    exact stabilizationGraft_preservesBoundary
      x H levels hH
  have hFfix :
      FixesBelow n F := by
    dsimp [F]
    exact stabilizationGraft_fixesBelow
      x H levels hH
  refine ⟨graftLevelMap n levels, F,
    hFcommon, hFboundary, hFfix, ?_⟩
  intro l z hzlevel hxz
  have hnl : n ≤ l := by
    let i0 : Fin d := ⟨0, hd⟩
    have hp := hxz i0
    have hlen := hp.length_le
    rw [x.2 i0, hzlevel i0] at hlen
    exact hlen
  let tails : Fin d → Node ι :=
    fun i => (z i).drop n
  have htails :
      ∀ i, (tails i).length = l - n := by
    intro i
    dsimp [tails]
    rw [List.length_drop, hzlevel i]
  let zeros : Fin d → Node ι :=
    fun _ => []
  have hzeros :
      ∀ i, (zeros i).length = 0 := by
    intro i
    rfl
  have hcTail :=
    hmono (l - n) tails htails
  have hcZero :=
    hmono 0 zeros hzeros
  have hcolorEq : c tails = c zeros :=
    hcTail.trans hcZero.symm
  have hmapZ :
      mapTuple F z =
        fun i => x.1 i ++ (H i).toFun (tails i) := by
    funext i
    dsimp [mapTuple, F, tails]
    exact stabilizationGraft_toFun_of_prefix
      x H levels hH i (z i) (hxz i)
  have hmapX :
      mapTuple F x.1 =
        fun i => x.1 i ++ (H i).toFun (zeros i) := by
    funext i
    dsimp [mapTuple, F, zeros]
    have hpref : (x.1 i).IsPrefix (x.1 i) :=
      List.prefix_refl _
    simpa [x.2 i] using
      (stabilizationGraft_toFun_of_prefix
        x H levels hH i (x.1 i) hpref)
  change
    (mapTuple F z ∈ A ↔ mapTuple F x.1 ∈ A)
  rw [hmapZ, hmapX]
  dsimp [c] at hcolorEq
  by_cases hzA :
      (fun i => x.1 i ++ (H i).toFun (tails i)) ∈ A
  · by_cases hxA :
        (fun i => x.1 i ++ (H i).toFun (zeros i)) ∈ A
    · exact ⟨fun _ => hxA, fun _ => hzA⟩
    · simp [hzA, hxA] at hcolorEq
  · by_cases hxA :
        (fun i => x.1 i ++ (H i).toFun (zeros i)) ∈ A
    · simp [hzA, hxA] at hcolorEq
    · exact ⟨fun h => (hzA h).elim,
        fun h => (hxA h).elim⟩

end HalpernLauchli
end Milliken
