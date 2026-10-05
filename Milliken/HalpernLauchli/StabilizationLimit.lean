import Milliken.HalpernLauchli.StabilizationFusion
import Milliken.Closed
import Milliken.FinitizationOrder
import RamseySpace.Closed

/-!
# Closedness limit of the stabilization fusion

The stabilization construction produces, in each front coordinate, a genuine
fusion sequence of strong trees: stage `n+1` lies below stage `n` and has
the same approximation through height `n+1`.

The first-application audit of the Abstract Ellentuck repository exposes the
precise noncircular fact needed here:

`Finitization.fusionComplete_of_isMetricallyClosed`

uses only A.2 and metric closedness, and therefore may be used while the
pigeonhole part of the present Halpern--Läuchli proof is still being built.
We use it coordinatewise instead of manually reconstructing a diagonal
strong embedding.

The protected approximations then imply that all coordinate limits retain
one common level set, and every stabilization identity is inherited from a
sufficiently late finite stage.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- A stabilization step is a genuine reduction of strong trees in every
front coordinate. -/
theorem stabilizationFusionState_succ_le
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin d) :
    StrongTreeSpace.le ι
      ((stabilizationFusionState hd hHDHL P (n + 1)).F i)
      ((stabilizationFusionState hd hHDHL P n).F i) := by
  let S := stabilizationFusionState hd hHDHL P n
  let step := nextStabilizationFusionStep hd hHDHL S
  change StrongTreeSpace.le ι (step.next.F i) (S.F i)
  refine ⟨step.factor i, ?_⟩
  have hfamily := congrFun step.nextFamily i
  simpa [compFamily] using hfamily

/-- The protected approximation at one fusion step is unchanged. -/
theorem stabilizationFusionState_succ_approx
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin d) :
    StrongTreeSpace.approx ι (n + 1)
        ((stabilizationFusionState hd hHDHL P (n + 1)).F i) =
      StrongTreeSpace.approx ι (n + 1)
        ((stabilizationFusionState hd hHDHL P n).F i) := by
  apply Subtype.ext
  funext s
  exact stabilizationFusionState_succ_agrees
    hd hHDHL P n i s.1 s.2

/-- The coordinate sequence underlying the stabilization fusion. -/
noncomputable def stabilizationCoordinateSequence
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) :
    ℕ → StrongEmbedding ι :=
  fun n => (stabilizationFusionState hd hHDHL P n).F i

/-- Each coordinate is a Ramsey-space fusion sequence starting at protected
height one. -/
theorem stabilizationCoordinateSequence_isFusion
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) :
    (StrongTreeSpace.S ι).IsFusionFrom 1
      (stabilizationCoordinateSequence hd hHDHL P i) := by
  intro n
  change
    StrongTreeSpace.le ι
        ((stabilizationFusionState hd hHDHL P (n + 1)).F i)
        ((stabilizationFusionState hd hHDHL P n).F i) ∧
      StrongTreeSpace.approx ι (1 + n)
          ((stabilizationFusionState hd hHDHL P (n + 1)).F i) =
        StrongTreeSpace.approx ι (1 + n)
          ((stabilizationFusionState hd hHDHL P n).F i)
  constructor
  · exact stabilizationFusionState_succ_le
      hd hHDHL P n i
  · simpa [Nat.add_comm] using
      (stabilizationFusionState_succ_approx
        hd hHDHL P n i)

/-- Closedness plus A.2 gives fusion completeness for the strong-tree
approximation system, independently of A.3 and A.4. -/
theorem strongTreeFusionComplete
    [Finite ι] [Nonempty ι] :
    RamseySpace.FusionComplete (StrongTreeSpace.S ι) :=
  RamseySpace.Finitization.fusionComplete_of_isMetricallyClosed
    (StrongTreeSpace.finitization (ι := ι))
    (StrongTreeSpace.isMetricallyClosed (ι := ι))

/-- Every front coordinate has a closedness-supplied fusion limit. -/
theorem exists_stabilizationCoordinateLimit
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) :
    ∃ X : StrongEmbedding ι,
      ∀ n,
        X ∈ (StrongTreeSpace.S ι).levelNeighborhood (1 + n)
          (stabilizationCoordinateSequence hd hHDHL P i n) :=
  (strongTreeFusionComplete (ι := ι)).limit
    1
    (stabilizationCoordinateSequence hd hHDHL P i)
    (stabilizationCoordinateSequence_isFusion
      hd hHDHL P i)

/-- Closedness-selected limit in one front coordinate. -/
noncomputable def stabilizationLimitEmbedding
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) :
    StrongEmbedding ι :=
  Classical.choose
    (exists_stabilizationCoordinateLimit hd hHDHL P i)

theorem stabilizationLimitEmbedding_mem
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (n : ℕ) :
    stabilizationLimitEmbedding hd hHDHL P i ∈
      (StrongTreeSpace.S ι).levelNeighborhood (1 + n)
        (stabilizationCoordinateSequence hd hHDHL P i n) :=
  Classical.choose_spec
    (exists_stabilizationCoordinateLimit hd hHDHL P i) n

/-- Coordinatewise closedness limits. -/
noncomputable def stabilizationLimitFamily
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    Fin d → StrongEmbedding ι :=
  stabilizationLimitEmbedding hd hHDHL P

/-- The common target level inherited from finite stage `n`. -/
noncomputable def stabilizationLimitLevels
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) : ℕ :=
  (stabilizationFusionState hd hHDHL P n).levels n

/-- A limit coordinate agrees with finite stage `n` on all source nodes
below height `n+1`. -/
theorem stabilizationLimit_toFun_eq_stage
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin d) (s : Node ι)
    (hs : s.length < n + 1) :
    (stabilizationLimitFamily hd hHDHL P i).toFun s =
      ((stabilizationFusionState hd hHDHL P n).F i).toFun s := by
  have happ :
      StrongTreeSpace.approx ι (1 + n)
          (stabilizationLimitFamily hd hHDHL P i) =
        StrongTreeSpace.approx ι (1 + n)
          ((stabilizationFusionState hd hHDHL P n).F i) :=
    (stabilizationLimitEmbedding_mem
      hd hHDHL P i n).2
  exact StrongTreeSpace.toFun_eq_of_approx_eq
    happ (by simpa [Nat.add_comm] using hs)

/-- Limit coordinates share the same target level on every source level. -/
theorem stabilizationLimit_sameLevel
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (s : Node ι) :
    ((stabilizationLimitFamily hd hHDHL P i).toFun s).length =
      stabilizationLimitLevels hd hHDHL P s.length := by
  rw [stabilizationLimit_toFun_eq_stage
    hd hHDHL P s.length i s (Nat.lt_succ_self _)]
  exact
    (stabilizationFusionState
      hd hHDHL P s.length).common.2 i s

/-- The inherited common level map is strictly increasing. -/
theorem stabilizationLimitLevels_strictMono
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    StrictMono (stabilizationLimitLevels hd hHDHL P) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let i0 : Fin d := ⟨0, hd⟩
  let r : Node ι := rayNode (ι := ι) n
  have hagree :
      ((stabilizationFusionState
          hd hHDHL P (n + 1)).F i0).toFun r =
        ((stabilizationFusionState
          hd hHDHL P n).F i0).toFun r :=
    stabilizationFusionState_succ_agrees
      hd hHDHL P n i0 r (by
        dsimp [r]
        rw [rayNode_length]
        omega)
  have hlevelEq :
      (stabilizationFusionState hd hHDHL P (n + 1)).levels n =
        (stabilizationFusionState hd hHDHL P n).levels n := by
    have hlen := congrArg List.length hagree
    rw [
      (stabilizationFusionState
        hd hHDHL P (n + 1)).common.2 i0 r,
      (stabilizationFusionState
        hd hHDHL P n).common.2 i0 r,
      rayNode_length] at hlen
    exact hlen
  have hlt :
      (stabilizationFusionState
          hd hHDHL P (n + 1)).levels n <
        (stabilizationFusionState
          hd hHDHL P (n + 1)).levels (n + 1) :=
    (stabilizationFusionState
      hd hHDHL P (n + 1)).common.1
      (Nat.lt_succ_self n)
  unfold stabilizationLimitLevels
  exact hlevelEq.symm.trans_lt hlt

/-- The closedness-selected coordinate limits still have one common level
set. -/
theorem stabilizationLimitFamily_commonLevels
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    HasCommonLevels
      (stabilizationLimitFamily hd hHDHL P)
      (stabilizationLimitLevels hd hHDHL P) := by
  refine ⟨stabilizationLimitLevels_strictMono
      hd hHDHL P, ?_⟩
  intro i s
  exact stabilizationLimit_sameLevel
    hd hHDHL P i s

/-- The front pullback by the closedness fusion limit satisfies the full
stabilization property (*). -/
theorem stabilizationLimit_stabilized
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    Stabilized
      (pullbackFront P
        (stabilizationLimitFamily hd hHDHL P)) := by
  intro y l z hzlevel hyl
  have hstage :
      StabilizedAtLevel
        (pullbackFront P
          (stabilizationFusionState hd hHDHL P l).F)
        y.length :=
    (stabilizationFusionState hd hHDHL P l).stabilized
      y.length hyl
  have hstageIff :=
    hstage y rfl l z hzlevel hyl

  rw [mem_lastSection_pullbackFront
        P (stabilizationLimitFamily hd hHDHL P) y z,
      mem_lastSection_pullbackFront
        P (stabilizationLimitFamily hd hHDHL P) y
        (truncateVector (y.length + 1) z)]
  rw [mem_lastSection_pullbackFront
        P (stabilizationFusionState hd hHDHL P l).F y z,
      mem_lastSection_pullbackFront
        P (stabilizationFusionState hd hHDHL P l).F y
        (truncateVector (y.length + 1) z)] at hstageIff

  have hzmap :
      mapTuple (stabilizationLimitFamily hd hHDHL P) z =
        mapTuple
          (stabilizationFusionState hd hHDHL P l).F z := by
    funext i
    dsimp [mapTuple]
    exact stabilizationLimit_toFun_eq_stage
      hd hHDHL P l i (z i) (by
        rw [hzlevel i]
        omega)

  have htruncLevel :
      IsLevelVectorAt (y.length + 1)
        (truncateVector (y.length + 1) z) :=
    truncateVector_length hzlevel (by omega)
  have htruncMap :
      mapTuple (stabilizationLimitFamily hd hHDHL P)
          (truncateVector (y.length + 1) z) =
        mapTuple
          (stabilizationFusionState hd hHDHL P l).F
          (truncateVector (y.length + 1) z) := by
    funext i
    dsimp [mapTuple]
    exact stabilizationLimit_toFun_eq_stage
      hd hHDHL P l i
      (truncateVector (y.length + 1) z i)
      (by
        rw [htruncLevel i]
        omega)

  simpa [pullbackProduct, hzmap, htruncMap] using hstageIff

end HalpernLauchli
end Milliken
