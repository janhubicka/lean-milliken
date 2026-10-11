import Milliken.GeneralTree.MixedSuccessors

/-!
# Genuine protected mixed-cone strong subtree

Let D be the background strong tree and X the chosen refinement
whose used source-level n frontier lies in D's source-level j
frontier. If their future selected ambient levels coincide,
retain D's complete source levels through j, follow X in used
frontier cones, and continue D in unused frontier cones.

The resulting mixed carrier is a genuine infinite strong subtree
of the arbitrary ambient tree U. No uniform branching degree
or global finite alphabet is assumed.

Exact prefix preservation, common refinement and the used-X
confinement law are also exported. The remaining A.3(2)
obligation is to supply an appropriate D whose first j+1
levels equal B's prescribed depth prefix and whose future
selected levels agree with X; this is addressed by the
prefix-preserving thinning and protected-index constructions.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- Replace the used selected-frontier cones of D with X,
while retaining the full D prefix and continuing unused
cones within D. This is a genuine strong subtree of U. -/
noncomputable def mixedStrong
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t)) :
    StrongSubtree U where
  carrier := D.mixedCarrier X j n
  levels := D.levels
  levels_strictMono := D.levels_strictMono
  root := D.root
  root_mem := D.mixedCarrier_root_mem X j n hfront
  root_level := D.root_level
  root_below := by
    intro z hz
    exact D.mixedCarrier_root_below X j n hfront hz
  carrier_levels := by
    intro z hz
    exact D.mixedCarrier_levels X j n hlevels hz
  predecessor_exists := by
    intro k z hz hzlevel
    exact D.mixedCarrier_predecessor_exists X j n k
      hfront hlevels z hz hzlevel
  successor_unique := by
    intro k x hx hxlevel y hxy
    exact D.mixedCarrier_successor_unique X j n k
      hfront hlevels x hx hxlevel y hxy

/-- The genuine mixed strong tree has precisely the
explicit prefix-plus-two-cones carrier. -/
@[simp] theorem mixedStrong_carrier
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t)) :
    (D.mixedStrong X j n hfront hlevels).carrier =
      D.mixedCarrier X j n := rfl

/-- All source levels before the protected frontier remain
exactly D's old selected source levels. -/
theorem mixedStrong_sourceLevel_before
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    {k : ℕ} (hk : k < j) :
    (D.mixedStrong X j n hfront hlevels).sourceLevel k =
      D.sourceLevel k := by
  change {z : U | z ∈ D.mixedCarrier X j n ∧
    U.level z = D.levels k} = D.sourceLevel k
  exact D.mixedCarrier_level_before X j n hfront hk

/-- The frontier itself remains the *entire*
selected j-th source level of D. -/
theorem mixedStrong_sourceLevel_at
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t)) :
    (D.mixedStrong X j n hfront hlevels).sourceLevel j =
      D.sourceLevel j := by
  change {z : U | z ∈ D.mixedCarrier X j n ∧
    U.level z = D.levels j} = D.sourceLevel j
  exact D.mixedCarrier_level_at X j n hfront

/-- The full old finite strong prefix up to j
is preserved exactly. -/
theorem mixedStrong_initialPart
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t)) :
    (D.mixedStrong X j n hfront hlevels).initialPart j =
      D.initialPart j := by
  let M := D.mixedStrong X j n hfront hlevels
  ext z
  constructor
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hzk : z ∈ M.sourceLevel k := ⟨hz, hzlevel⟩
    have hsource : M.sourceLevel k = D.sourceLevel k :=
      D.mixedStrong_sourceLevel_before X j n
        hfront hlevels hk
    rw [hsource] at hzk
    exact ⟨hzk.1, k, hk, hzk.2⟩
  · rintro ⟨hz, k, hk, hzlevel⟩
    have hzk : z ∈ D.sourceLevel k := ⟨hz, hzlevel⟩
    have hsource : M.sourceLevel k = D.sourceLevel k :=
      D.mixedStrong_sourceLevel_before X j n
        hfront hlevels hk
    rw [← hsource] at hzk
    exact ⟨hzk.1, k, hk, hzk.2⟩

/-- The mixed strong subtree preserves D's full finite
approximation of height j+1, including the unused frontier nodes. -/
theorem mixedStrong_approx_succ
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t)) :
    r (j + 1) (D.mixedStrong X j n hfront hlevels) =
      r (j + 1) D := by
  let M := D.mixedStrong X j n hfront hlevels
  apply FiniteApprox.ext_carrier
  change M.initialPart (j + 1) = D.initialPart (j + 1)
  calc
    M.initialPart (j + 1) =
        M.initialPart j ∪ M.sourceLevel j :=
      M.initialPart_succ j
    _ = D.initialPart j ∪ D.sourceLevel j := by
      rw [D.mixedStrong_initialPart X j n hfront hlevels,
        D.mixedStrong_sourceLevel_at X j n hfront hlevels]
    _ = D.initialPart (j + 1) :=
      (D.initialPart_succ j).symm

/-- If both D and X refine B, the mixed strong subtree
also refines B. -/
theorem mixedStrong_refines_common
    (B D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    (hDB : D.Refines B) (hXB : X.Refines B) :
    (D.mixedStrong X j n hfront hlevels).Refines B := by
  intro z hz
  exact mixedCarrier_subset_of_common_refinement
    B D X j n hDB hXB hz

/-- Every node of the final mixed strong tree in a used
X-frontier cone belongs to X. Unused D-cones may lie
outside X, which is necessary for preserving the full
depth frontier in A.3(2). -/
theorem mixedStrong_used_sector_in_X
    (D X : StrongSubtree U) (j n : ℕ)
    (hfront : X.sourceLevel n ⊆ D.sourceLevel j)
    (hlevels : ∀ t : ℕ, D.levels (j + t) =
      X.levels (n + t))
    {z : U}
    (hz : z ∈ (D.mixedStrong X j n hfront hlevels).carrier)
    (hcone : z ∈ U.upwardCones (X.sourceLevel n)) :
    z ∈ X.carrier :=
  D.mixedCarrier_used_sector_in_X X j n hfront hz hcone

end StrongSubtree
end GeneralTree
end Milliken
