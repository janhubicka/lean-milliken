import Milliken.GeneralTree.ProtectedFusionLimit
import Milliken.GeneralTree.HeterogeneousDensity

/-!
# Simultaneous protected fusion of heterogeneous strong-tree families

Apply the general-tree finite-code limit independently in each
coordinate of a finite protected fusion sequence. If every finite
stage has one common selected ambient-level map, the limits
retain a common level map as well: the nth limiting level is
exactly the level used at source index n by finite stage n+1.

Each limit coordinate strongly refines every finite stage,
and its nth source level is exactly the protected nth source
level of stage n+1. The positive-dimension assumption is used
only to deduce strict monotonicity of the shared level sequence.

All of this is purely geometric, with no A.4, Ramsey theorem,
homogeneous alphabet, or bound on local branching.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- A protected sequence of synchronized strong-tree families. -/
structure HeterogeneousProtectedFusion
    (U : AmbientTree) (d : ℕ) where
  family : ℕ → Fin d → StrongSubtree U
  commonLevels : ℕ → ℕ → ℕ
  synchronized : ∀ n i, (family n i).levels = commonLevels n
  refines : ∀ n i, (family (n + 1) i).Refines (family n i)
  protects : ∀ n i,
    r (n + 1) (family (n + 1) i) =
      r (n + 1) (family n i)

/-- Coordinatewise noncircular fusion limit. -/
noncomputable def HeterogeneousProtectedFusion.limit
    (S : HeterogeneousProtectedFusion U d) :
    Fin d → StrongSubtree U :=
  fun i =>
    generalFusionLimit (fun n => S.family n i) (fun n => S.protects n i)

/-- The common selected ambient-level sequence of the limit. -/
def HeterogeneousProtectedFusion.limitLevels
    (S : HeterogeneousProtectedFusion U d) (n : ℕ) : ℕ :=
  S.commonLevels (n + 1) n

/-- Exact source-level agreement between the limit and the
corresponding protected finite stage. -/
theorem HeterogeneousProtectedFusion.limit_sourceLevel
    (S : HeterogeneousProtectedFusion U d)
    (i : Fin d) (n : ℕ) :
    (S.limit i).sourceLevel n = (S.family (n + 1) i).sourceLevel n :=
  generalFusionLimit_sourceLevel
    (fun k => S.family k i) (fun k => S.protects k i) n

/-- Exact finite approximation agreement with stage n. -/
theorem HeterogeneousProtectedFusion.limit_approx
    (S : HeterogeneousProtectedFusion U d)
    (i : Fin d) (n : ℕ) :
    r n (S.limit i) = r n (S.family n i) :=
  generalFusionLimit_approx
    (fun k => S.family k i) (fun k => S.protects k i) n

/-- The limit shares the same selected ambient level at each index
in every coordinate, obtained from a single finite stage. -/
theorem HeterogeneousProtectedFusion.limit_levels
    (S : HeterogeneousProtectedFusion U d)
    (i : Fin d) :
    (S.limit i).levels = S.limitLevels := by
  funext n
  obtain ⟨x, hx⟩ := (S.limit i).sourceLevel_nonempty n
  have hstage : x ∈ (S.family (n + 1) i).sourceLevel n := by
    rw [← S.limit_sourceLevel i n]
    exact hx
  calc
    (S.limit i).levels n = U.level x := hx.2.symm
    _ = (S.family (n + 1) i).levels n := hstage.2
    _ = S.limitLevels n := congrFun (S.synchronized (n + 1) i) n

/-- In positive dimension the common limiting level sequence
is strictly increasing. -/
theorem HeterogeneousProtectedFusion.limitLevels_strictMono
    (S : HeterogeneousProtectedFusion U d)
    (hd : 0 < d) :
    StrictMono S.limitLevels := by
  let i0 : Fin d := ⟨0, hd⟩
  have h := (S.limit i0).levels_strictMono
  rw [S.limit_levels i0] at h
  exact h

/-- Every limit coordinate refines every finite stage. -/
theorem HeterogeneousProtectedFusion.limit_refines
    (S : HeterogeneousProtectedFusion U d)
    (n : ℕ) (i : Fin d) :
    (S.limit i).Refines (S.family n i) :=
  generalFusionLimit_refines
    (fun k => S.family k i)
    (fun k => S.refines k i)
    (fun k => S.protects k i)
    n

/-- A limiting tuple on source level n already lies in the
actual source-level-n product of finite stage n+1. -/
theorem HeterogeneousProtectedFusion.limit_tuple_at_stage
    (S : HeterogeneousProtectedFusion U d)
    (n : ℕ)
    (x : HeterogeneousLevelTuple S.limit n) :
    ∀ i, x.1 i ∈ (S.family (n + 1) i).sourceLevel n := by
  intro i
  rw [← S.limit_sourceLevel i n]
  exact x.2 i

end GeneralTree
end Milliken
