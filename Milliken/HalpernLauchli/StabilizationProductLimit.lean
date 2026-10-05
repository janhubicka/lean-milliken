import Milliken.HalpernLauchli.StabilizationProductFusion

/-!
# Closedness limit of the product stabilization fusion

Every coordinate of the product-level stabilization sequence is a fusion
sequence of strong trees.  We again use the noncircular closedness theorem
from the Abstract Ellentuck repository to obtain limits, now simultaneously
for all `d+1` coordinates.

Because each finite state has one common level map, the coordinatewise limits
still share a common level map.  A stabilization identity at source level
`l` can then be read from finite stage `l`, where all nodes occurring in
that identity are protected.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

theorem productStabilizationState_succ_le
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin (d + 1)) :
    StrongTreeSpace.le ι
      ((productStabilizationState hd hHDHL P (n + 1)).E i)
      ((productStabilizationState hd hHDHL P n).E i) := by
  let S := productStabilizationState hd hHDHL P n
  let step := nextProductStabilizationStep hd hHDHL S
  change StrongTreeSpace.le ι (step.next.E i) (S.E i)
  refine ⟨step.factor i, ?_⟩
  have hfamily := congrFun step.nextFamily i
  simpa [compFamily] using hfamily

theorem productStabilizationState_succ_approx
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin (d + 1)) :
    StrongTreeSpace.approx ι (n + 1)
        ((productStabilizationState hd hHDHL P (n + 1)).E i) =
      StrongTreeSpace.approx ι (n + 1)
        ((productStabilizationState hd hHDHL P n).E i) := by
  apply Subtype.ext
  funext s
  exact productStabilizationState_succ_agrees
    hd hHDHL P n i s.1 s.2

noncomputable def productStabilizationCoordinateSequence
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) :
    ℕ → StrongEmbedding ι :=
  fun n => (productStabilizationState hd hHDHL P n).E i

theorem productStabilizationCoordinateSequence_isFusion
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) :
    (StrongTreeSpace.S ι).IsFusionFrom 1
      (productStabilizationCoordinateSequence
        hd hHDHL P i) := by
  intro n
  change
    StrongTreeSpace.le ι
        ((productStabilizationState hd hHDHL P (n + 1)).E i)
        ((productStabilizationState hd hHDHL P n).E i) ∧
      StrongTreeSpace.approx ι (1 + n)
          ((productStabilizationState hd hHDHL P (n + 1)).E i) =
        StrongTreeSpace.approx ι (1 + n)
          ((productStabilizationState hd hHDHL P n).E i)
  constructor
  · exact productStabilizationState_succ_le
      hd hHDHL P n i
  · rw [Nat.add_comm 1 n]
    exact productStabilizationState_succ_approx
      hd hHDHL P n i

theorem exists_productStabilizationCoordinateLimit
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) :
    ∃ X : StrongEmbedding ι,
      ∀ n,
        X ∈ (StrongTreeSpace.S ι).levelNeighborhood (1 + n)
          (productStabilizationCoordinateSequence
            hd hHDHL P i n) :=
  (strongTreeFusionComplete (ι := ι)).limit
    1
    (productStabilizationCoordinateSequence
      hd hHDHL P i)
    (productStabilizationCoordinateSequence_isFusion
      hd hHDHL P i)

noncomputable def productStabilizationLimitEmbedding
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) :
    StrongEmbedding ι :=
  Classical.choose
    (exists_productStabilizationCoordinateLimit
      hd hHDHL P i)

theorem productStabilizationLimitEmbedding_mem
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) (n : ℕ) :
    productStabilizationLimitEmbedding hd hHDHL P i ∈
      (StrongTreeSpace.S ι).levelNeighborhood (1 + n)
        (productStabilizationCoordinateSequence
          hd hHDHL P i n) :=
  Classical.choose_spec
    (exists_productStabilizationCoordinateLimit
      hd hHDHL P i) n

noncomputable def productStabilizationLimitFamily
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    Fin (d + 1) → StrongEmbedding ι :=
  productStabilizationLimitEmbedding hd hHDHL P

noncomputable def productStabilizationLimitLevels
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) : ℕ :=
  (productStabilizationState hd hHDHL P n).levels n

theorem productStabilizationLimit_toFun_eq_stage
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) (i : Fin (d + 1)) (s : Node ι)
    (hs : s.length < n + 1) :
    (productStabilizationLimitFamily hd hHDHL P i).toFun s =
      ((productStabilizationState hd hHDHL P n).E i).toFun s := by
  have happ :
      StrongTreeSpace.approx ι (1 + n)
          (productStabilizationLimitFamily hd hHDHL P i) =
        StrongTreeSpace.approx ι (1 + n)
          ((productStabilizationState hd hHDHL P n).E i) :=
    (productStabilizationLimitEmbedding_mem
      hd hHDHL P i n).2
  exact StrongTreeSpace.toFun_eq_of_approx_eq
    ι happ (by simpa [Nat.add_comm] using hs)

theorem productStabilizationLimit_sameLevel
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin (d + 1)) (s : Node ι) :
    ((productStabilizationLimitFamily hd hHDHL P i).toFun s).length =
      productStabilizationLimitLevels hd hHDHL P s.length := by
  rw [productStabilizationLimit_toFun_eq_stage
    hd hHDHL P s.length i s (Nat.lt_succ_self _)]
  exact
    (productStabilizationState
      hd hHDHL P s.length).common.2 i s

theorem productStabilizationLimitLevels_strictMono
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    StrictMono (productStabilizationLimitLevels
      hd hHDHL P) := by
  apply strictMono_nat_of_lt_succ
  intro n
  let i0 : Fin (d + 1) := Fin.last d
  let r : Node ι := rayNode (ι := ι) n
  have hagree :
      ((productStabilizationState
          hd hHDHL P (n + 1)).E i0).toFun r =
        ((productStabilizationState
          hd hHDHL P n).E i0).toFun r :=
    productStabilizationState_succ_agrees
      hd hHDHL P n i0 r (by
        dsimp [r]
        rw [rayNode_length]
        omega)
  have hlevelEq :
      (productStabilizationState
          hd hHDHL P (n + 1)).levels n =
        (productStabilizationState
          hd hHDHL P n).levels n := by
    have hlen := congrArg List.length hagree
    rw [
      (productStabilizationState
        hd hHDHL P (n + 1)).common.2 i0 r,
      (productStabilizationState
        hd hHDHL P n).common.2 i0 r,
      rayNode_length] at hlen
    exact hlen
  have hlt :
      (productStabilizationState
          hd hHDHL P (n + 1)).levels n <
        (productStabilizationState
          hd hHDHL P (n + 1)).levels (n + 1) :=
    (productStabilizationState
      hd hHDHL P (n + 1)).common.1
      (Nat.lt_succ_self n)
  unfold productStabilizationLimitLevels
  exact hlevelEq.symm.trans_lt hlt

theorem productStabilizationLimitFamily_commonLevels
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    HasCommonLevels
      (productStabilizationLimitFamily hd hHDHL P)
      (productStabilizationLimitLevels hd hHDHL P) := by
  refine ⟨productStabilizationLimitLevels_strictMono
      hd hHDHL P, ?_⟩
  intro i s
  exact productStabilizationLimit_sameLevel
    hd hHDHL P i s

/-- The fully reindexed pullback is stabilized. -/
theorem productStabilizationLimit_stabilized
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    Stabilized
      (pullbackProduct
        (productStabilizationLimitFamily hd hHDHL P) P) := by
  intro y l z hzlevel hyl
  have hstage :
      StabilizedAtLevel
        (pullbackProduct
          (productStabilizationState hd hHDHL P l).E P)
        y.length :=
    (productStabilizationState hd hHDHL P l).stabilized
      y.length hyl
  have hstageIff :=
    hstage y rfl l z hzlevel hyl

  have hfullMap :
      mapTuple (productStabilizationLimitFamily hd hHDHL P)
          (appendLast z y) =
        mapTuple (productStabilizationState hd hHDHL P l).E
          (appendLast z y) := by
    funext i
    cases i using Fin.lastCases with
    | last =>
        dsimp [mapTuple, appendLast]
        exact productStabilizationLimit_toFun_eq_stage
          hd hHDHL P l (Fin.last d) y (by omega)
    | cast j =>
        dsimp [mapTuple, appendLast]
        exact productStabilizationLimit_toFun_eq_stage
          hd hHDHL P l (Fin.castSucc j) (z j) (by
            rw [hzlevel j]
            omega)

  have htruncLevel :
      IsLevelVectorAt (y.length + 1)
        (truncateVector (y.length + 1) z) :=
    truncateVector_length hzlevel (by omega)
  have htruncMap :
      mapTuple (productStabilizationLimitFamily hd hHDHL P)
          (appendLast (truncateVector (y.length + 1) z) y) =
        mapTuple (productStabilizationState hd hHDHL P l).E
          (appendLast (truncateVector (y.length + 1) z) y) := by
    funext i
    cases i using Fin.lastCases with
    | last =>
        dsimp [mapTuple, appendLast]
        exact productStabilizationLimit_toFun_eq_stage
          hd hHDHL P l (Fin.last d) y (by omega)
    | cast j =>
        dsimp [mapTuple, appendLast]
        exact productStabilizationLimit_toFun_eq_stage
          hd hHDHL P l (Fin.castSucc j)
          (truncateVector (y.length + 1) z j) (by
            rw [htruncLevel j]
            omega)

  change
    (mapTuple (productStabilizationLimitFamily hd hHDHL P)
        (appendLast z y) ∈ P ↔
      mapTuple (productStabilizationLimitFamily hd hHDHL P)
        (appendLast (truncateVector (y.length + 1) z) y) ∈ P)
  change
    (mapTuple (productStabilizationState hd hHDHL P l).E
        (appendLast z y) ∈ P ↔
      mapTuple (productStabilizationState hd hHDHL P l).E
        (appendLast (truncateVector (y.length + 1) z) y) ∈ P)
      at hstageIff
  simpa [hfullMap, htruncMap] using hstageIff

end HalpernLauchli
end Milliken
