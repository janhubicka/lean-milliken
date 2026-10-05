import Milliken.HalpernLauchli.StabilizationFusion
import Milliken.BranchEmbedding

/-!
# Diagonal limit of the stabilization fusion

The finite fusion sequence agrees on longer and longer source prefixes.
Therefore each source node eventually has a permanent image.  Reading the
image of a node from the first stage which protects it gives a diagonal
limit map.

The branch/level packaging theorem in `BranchEmbedding` turns this map into
a strong embedding in every front coordinate.  Since all finite stages use
common levels, the limit family also has one common level map.  Finally, any
particular stabilization identity can be checked in a sufficiently late
finite stage, so the front pullback by the limit family is fully stabilized.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

/-- Arbitrary later fusion stages agree with an earlier stage on the prefix
already protected by that earlier stage. -/
theorem stabilizationFusionState_agrees_of_le
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    {p q : ℕ} (hpq : p ≤ q)
    (i : Fin d) (s : Node ι)
    (hs : s.length < p + 1) :
    ((stabilizationFusionState hd hHDHL P q).F i).toFun s =
      ((stabilizationFusionState hd hHDHL P p).F i).toFun s := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hpq
      subst p
      rfl
  | succ q ih =>
      by_cases hp : p = q + 1
      · subst p
        rfl
      · have hpq' : p ≤ q := by omega
        have hsq : s.length < q + 1 := by
          exact hs.trans_le (Nat.add_le_add_right hpq' 1)
        calc
          ((stabilizationFusionState
              hd hHDHL P (q + 1)).F i).toFun s =
              ((stabilizationFusionState
                hd hHDHL P q).F i).toFun s :=
            stabilizationFusionState_succ_agrees
              hd hHDHL P q i s hsq
          _ =
              ((stabilizationFusionState
                hd hHDHL P p).F i).toFun s :=
            ih hpq' i s hs

/-- Permanent image of one source node in the diagonal fusion limit. -/
noncomputable def stabilizationLimitFun
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (s : Node ι) : Node ι :=
  ((stabilizationFusionState
      hd hHDHL P (s.length + 1)).F i).toFun s

/-- The common level assigned to source level `n` in the diagonal limit. -/
noncomputable def stabilizationLimitLevels
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (n : ℕ) : ℕ :=
  (stabilizationFusionState
    hd hHDHL P (n + 1)).levels n

theorem stabilizationLimitFun_sameLevel
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (s : Node ι) :
    (stabilizationLimitFun hd hHDHL P i s).length =
      stabilizationLimitLevels hd hHDHL P s.length := by
  unfold stabilizationLimitFun stabilizationLimitLevels
  exact
    (stabilizationFusionState
      hd hHDHL P (s.length + 1)).common.2 i s

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
          hd hHDHL P (n + 2)).F i0).toFun r =
        ((stabilizationFusionState
          hd hHDHL P (n + 1)).F i0).toFun r := by
    have hs : r.length < (n + 1) + 1 := by
      dsimp [r]
      rw [rayNode_length]
      omega
    simpa [Nat.add_assoc] using
      (stabilizationFusionState_succ_agrees
        hd hHDHL P (n + 1) i0 r hs)
  have hlen := congrArg List.length hagree
  have hlevelEq :
      (stabilizationFusionState
          hd hHDHL P (n + 2)).levels n =
        (stabilizationFusionState
          hd hHDHL P (n + 1)).levels n := by
    simpa [r, rayNode_length] using hlen
  have hlt :
      (stabilizationFusionState
          hd hHDHL P (n + 2)).levels n <
        (stabilizationFusionState
          hd hHDHL P (n + 2)).levels (n + 1) :=
    (stabilizationFusionState
      hd hHDHL P (n + 2)).common.1
      (Nat.lt_succ_self n)
  unfold stabilizationLimitLevels
  calc
    (stabilizationFusionState
        hd hHDHL P (n + 1)).levels n =
      (stabilizationFusionState
        hd hHDHL P (n + 2)).levels n :=
      hlevelEq.symm
    _ <
      (stabilizationFusionState
        hd hHDHL P (n + 2)).levels (n + 1) := hlt

theorem stabilizationLimitFun_branch
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (s : Node ι) (a : ι) :
    (child (stabilizationLimitFun hd hHDHL P i s) a).IsPrefix
      (stabilizationLimitFun
        hd hHDHL P i (child s a)) := by
  let n := s.length + 1
  have hagree :
      ((stabilizationFusionState
          hd hHDHL P (n + 1)).F i).toFun s =
        ((stabilizationFusionState
          hd hHDHL P n).F i).toFun s := by
    exact stabilizationFusionState_succ_agrees
      hd hHDHL P n i s (by
        dsimp [n]
        omega)
  have hbranch :=
    ((stabilizationFusionState
      hd hHDHL P (n + 1)).F i).branch s a
  rw [hagree] at hbranch
  simpa [stabilizationLimitFun, n, child,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbranch

/-- Coordinate strong embedding obtained from the diagonal limit. -/
noncomputable def stabilizationLimitEmbedding
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) :
    StrongEmbedding ι :=
  StrongEmbedding.ofBranchLevels
    (stabilizationLimitFun hd hHDHL P i)
    (stabilizationLimitLevels hd hHDHL P)
    (stabilizationLimitLevels_strictMono hd hHDHL P)
    (stabilizationLimitFun_sameLevel hd hHDHL P i)
    (stabilizationLimitFun_branch hd hHDHL P i)

@[simp] theorem stabilizationLimitEmbedding_toFun
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    (i : Fin d) (s : Node ι) :
    (stabilizationLimitEmbedding hd hHDHL P i).toFun s =
      stabilizationLimitFun hd hHDHL P i s := by
  rfl

/-- The coordinatewise diagonal limit family. -/
noncomputable def stabilizationLimitFamily
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι)) :
    Fin d → StrongEmbedding ι :=
  stabilizationLimitEmbedding hd hHDHL P

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
  exact stabilizationLimitFun_sameLevel
    hd hHDHL P i s

/-- On every finite source prefix, the diagonal limit agrees with any
sufficiently late finite fusion stage. -/
theorem stabilizationLimit_toFun_eq_stage
    [Finite ι] [Nonempty ι]
    {d : ℕ} (hd : 0 < d)
    (hHDHL : HDHL ι d)
    (P : Set (Fin (d + 1) → Node ι))
    {N : ℕ} (i : Fin d) (s : Node ι)
    (hs : s.length < N) :
    (stabilizationLimitFamily hd hHDHL P i).toFun s =
      ((stabilizationFusionState hd hHDHL P N).F i).toFun s := by
  rw [stabilizationLimitEmbedding_toFun]
  unfold stabilizationLimitFun
  have hle : s.length + 1 ≤ N := by omega
  symm
  exact stabilizationFusionState_agrees_of_le
    hd hHDHL P hle i s (by omega)

/-- The front pullback by the diagonal family satisfies the full
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
  let k := y.length
  let N := l + 1
  have hkN : k < N := by
    dsimp [k, N]
    omega
  have hstage :
      StabilizedAtLevel
        (pullbackFront P
          (stabilizationFusionState hd hHDHL P N).F) k :=
    (stabilizationFusionState
      hd hHDHL P N).stabilized k hkN
  have hy : y.length = k := rfl
  have hstageIff :=
    hstage y hy l z hzlevel hyl
  rw [mem_lastSection_pullbackFront
        P (stabilizationLimitFamily hd hHDHL P) y z,
      mem_lastSection_pullbackFront
        P (stabilizationLimitFamily hd hHDHL P) y
        (truncateVector (y.length + 1) z)]
  rw [mem_lastSection_pullbackFront
        P (stabilizationFusionState hd hHDHL P N).F y z,
      mem_lastSection_pullbackFront
        P (stabilizationFusionState hd hHDHL P N).F y
        (truncateVector (y.length + 1) z)] at hstageIff
  have hzmap :
      mapTuple (stabilizationLimitFamily hd hHDHL P) z =
        mapTuple
          (stabilizationFusionState hd hHDHL P N).F z := by
    funext i
    dsimp [mapTuple]
    exact stabilizationLimit_toFun_eq_stage
      hd hHDHL P i (z i) (by
        rw [hzlevel i]
        dsimp [N]
        omega)
  have htruncLevel :
      IsLevelVectorAt (y.length + 1)
        (truncateVector (y.length + 1) z) :=
    truncateVector_length hzlevel (by omega)
  have htruncMap :
      mapTuple (stabilizationLimitFamily hd hHDHL P)
          (truncateVector (y.length + 1) z) =
        mapTuple
          (stabilizationFusionState hd hHDHL P N).F
          (truncateVector (y.length + 1) z) := by
    funext i
    dsimp [mapTuple]
    exact stabilizationLimit_toFun_eq_stage
      hd hHDHL P i
      (truncateVector (y.length + 1) z i)
      (by
        rw [htruncLevel i]
        dsimp [N]
        omega)
  simpa [pullbackProduct, hzmap, htruncMap] using hstageIff

end HalpernLauchli
end Milliken
