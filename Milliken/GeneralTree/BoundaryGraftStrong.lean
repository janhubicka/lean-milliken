import Milliken.GeneralTree.BoundaryGraftSuccessor

/-!
# Actual heterogeneous boundary graft as an infinite strong subtree

This packages the predecessor and ambient-successor proofs into a genuine
StrongSubtree, for any finite family of strong refinements of the actual
source-boundary cones of T with synchronized selected levels.

The empty stem is handled by its unique coordinate tree. For every
positive stem, we keep the first n selected T levels and graft the
coordinate strong trees at their (potentially later) synchronized
initial ambient level.

This is the inverse realization half of the finite-boundary encoding
needed for Todorčević Lemma 6.1 (A.4). It does not assert the separate
heterogeneous product Halpern--Läuchli theorem.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A genuine strong subtree graft for a nonempty finite prefix. -/
noncomputable def boundaryGraftStrongSucc
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T (n + 1) → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T (n + 1) i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    StrongSubtree U := {
  carrier := T.boundaryGraftCarrier (n + 1) F
  levels := T.boundaryGraftLevels (n + 1) M
  levels_strictMono :=
    T.boundaryGraftLevels_strictMono (n + 1) M hM
      (T.boundaryGraft_start_le (n + 1) F M hF hlevels)
  root := T.root
  root_mem := Or.inl
    ⟨T.root_mem, 0, Nat.zero_lt_succ n, T.root_level⟩
  root_level := by
    rw [T.boundaryGraftLevels_before
      (n + 1) M (Nat.zero_lt_succ n)]
    exact T.root_level
  root_below := by
    intro z hz
    exact T.root_below z
      (T.boundaryGraftCarrier_refines (n + 1) F hF hz)
  carrier_levels := by
    intro z hz
    rcases hz with hstem | htail
    · obtain ⟨_, k, hk, hzlevel⟩ := hstem
      refine ⟨k, ?_⟩
      exact hzlevel.trans
        (T.boundaryGraftLevels_before (n + 1) M hk).symm
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp htail
      obtain ⟨k, hzlevel⟩ := (F i).carrier_levels z hi
      refine ⟨n + 1 + k, ?_⟩
      calc
        U.level z = (F i).levels k := hzlevel
        _ = M k := congrFun (hlevels i) k
        _ = T.boundaryGraftLevels (n + 1) M (n + 1 + k) :=
          (T.boundaryGraftLevels_at (n + 1) M k).symm
  predecessor_exists := by
    intro k z hz hzlevel
    exact T.boundaryGraft_predecessor_succ n F M
      hF hlevels hM k z hz hzlevel
  successor_unique := by
    intro k x hx hxlevel y hxy
    exact T.boundaryGraft_successor_succ n F M
      hF hlevels hM k x hx hxlevel y hxy
}

/-- Graft a synchronized family of strong boundary-cone refinements.
The height-zero case uses its unique T-boundary coordinate directly. -/
noncomputable def boundaryGraftStrong
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    StrongSubtree U := by
  cases n with
  | zero =>
      let i : SourceBoundary T 0 :=
        Classical.choice (sourceBoundary_nonempty T 0)
      exact F i
  | succ k =>
      exact T.boundaryGraftStrongSucc k F M hF hlevels hM

/-- The actual graft has exactly the explicitly defined candidate carrier. -/
theorem boundaryGraftStrong_carrier
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    (T.boundaryGraftStrong n F M hF hlevels hM).carrier =
      T.boundaryGraftCarrier n F := by
  cases n with
  | zero =>
      let i : SourceBoundary T 0 :=
        Classical.choice (sourceBoundary_nonempty T 0)
      change (F i).carrier = T.boundaryGraftCarrier 0 F
      exact (T.boundaryGraftCarrier_zero F i).symm
  | succ k =>
      rfl

/-- The selected ambient levels of the graft are exactly the old
initial levels followed by the coordinate common level sequence. -/
theorem boundaryGraftStrong_levels
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    (T.boundaryGraftStrong n F M hF hlevels hM).levels =
      T.boundaryGraftLevels n M := by
  cases n with
  | zero =>
      let i : SourceBoundary T 0 :=
        Classical.choice (sourceBoundary_nonempty T 0)
      change (F i).levels = T.boundaryGraftLevels 0 M
      rw [hlevels i]
      funext k
      exact (T.boundaryGraftLevels_at 0 M k).symm
  | succ k =>
      rfl

/-- Every graft node lies in the original strong tree. -/
theorem boundaryGraftStrong_refines
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    (T.boundaryGraftStrong n F M hF hlevels hM).Refines T := by
  intro z hz
  rw [T.boundaryGraftStrong_carrier n F M hF hlevels hM] at hz
  exact T.boundaryGraftCarrier_refines n F hF hz

/-- Every old source level strictly before the graft cut
survives exactly, with its ambient node identities unchanged. -/
theorem boundaryGraftStrong_sourceLevel_before
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M)
    {k : ℕ} (hk : k < n) :
    (T.boundaryGraftStrong n F M hF hlevels hM).sourceLevel k =
      T.sourceLevel k := by
  change
    {z : U |
      z ∈ (T.boundaryGraftStrong n F M hF hlevels hM).carrier ∧
      U.level z =
        (T.boundaryGraftStrong n F M hF hlevels hM).levels k} =
      T.sourceLevel k
  rw [T.boundaryGraftStrong_carrier n F M hF hlevels hM,
    T.boundaryGraftStrong_levels n F M hF hlevels hM,
    T.boundaryGraftLevels_before n M hk]
  exact T.boundaryGraft_level_before n F hF hk

/-- The graft retains exactly the first n selected source levels,
including the empty finite approximation at n=0. -/
theorem boundaryGraftStrong_approx
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    r n (T.boundaryGraftStrong n F M hF hlevels hM) = r n T := by
  let G := T.boundaryGraftStrong n F M hF hlevels hM
  apply FiniteApprox.ext_carrier
  change G.initialPart n = T.initialPart n
  ext z
  constructor
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hsource : z ∈ G.sourceLevel k := ⟨hz, hzlevel⟩
    have hsame : G.sourceLevel k = T.sourceLevel k :=
      T.boundaryGraftStrong_sourceLevel_before n F M
        hF hlevels hM hk
    rw [hsame] at hsource
    exact ⟨hsource.1, k, hk, hsource.2⟩
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hsource : z ∈ T.sourceLevel k := ⟨hz, hzlevel⟩
    have hsame : G.sourceLevel k = T.sourceLevel k :=
      T.boundaryGraftStrong_sourceLevel_before n F M
        hF hlevels hM hk
    rw [← hsame] at hsource
    exact ⟨hsource.1, k, hk, hsource.2⟩

/-- The graft's first new source level is precisely the
synchronized tuple of coordinate roots. -/
theorem boundaryGraftStrong_sourceLevel_at
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    (T.boundaryGraftStrong n F M hF hlevels hM).sourceLevel n =
      Set.range (fun i : SourceBoundary T n => (F i).root) := by
  change
    {z : U |
      z ∈ (T.boundaryGraftStrong n F M hF hlevels hM).carrier ∧
      U.level z =
        (T.boundaryGraftStrong n F M hF hlevels hM).levels n} =
      Set.range (fun i : SourceBoundary T n => (F i).root)
  rw [T.boundaryGraftStrong_carrier n F M hF hlevels hM,
    T.boundaryGraftStrong_levels n F M hF hlevels hM]
  have hlevelAt :
      T.boundaryGraftLevels n M n = M 0 := by
    simpa only [Nat.add_zero] using
      T.boundaryGraftLevels_at n M 0
  rw [hlevelAt]
  exact T.boundaryGraft_level_at n F M hF hlevels

/-- A one-step graft approximation is exactly the old
height-n stem plus its finite tuple of selected roots. -/
theorem boundaryGraftStrong_approx_succ_carrier
    (T : StrongSubtree U) (n : ℕ)
    (F : SourceBoundary T n → StrongSubtree U)
    (M : ℕ → ℕ)
    (hF : ∀ i, (F i).Refines (boundaryCones T n i))
    (hlevels : ∀ i, (F i).levels = M)
    (hM : StrictMono M) :
    (r (n + 1) (T.boundaryGraftStrong n F M hF hlevels hM)).carrier =
      (r n T).carrier ∪
        Set.range (fun i : SourceBoundary T n => (F i).root) := by
  let G := T.boundaryGraftStrong n F M hF hlevels hM
  calc
    (r (n + 1) G).carrier =
        G.initialPart n ∪ G.sourceLevel n :=
      G.initialPart_succ n
    _ = T.initialPart n ∪
        Set.range (fun i : SourceBoundary T n => (F i).root) := by
      rw [← T.boundaryGraftStrong_sourceLevel_at
        n F M hF hlevels hM]
      exact congrArg (fun a : SFinite U n =>
        a.carrier ∪ G.sourceLevel n)
        (T.boundaryGraftStrong_approx n F M hF hlevels hM)
    _ = (r n T).carrier ∪
        Set.range (fun i : SourceBoundary T n => (F i).root) := rfl

end StrongSubtree
end GeneralTree
end Milliken
