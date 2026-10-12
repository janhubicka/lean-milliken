import Milliken.GeneralTree.HeterogeneousLemma315Proof

/-!
# The heterogeneous Lemma 3.16 density tower

This port of Todorčević's Lemma 3.16 tower works with actual selected
source levels of non-isomorphic locally finitely branching strong trees.
At step p it uses the proved heterogeneous, tail-normalized Lemma 3.15
to obtain a cone-dense set of last-coordinate witnesses on which every
source-n(p+1)-dense front matrix is source-n(p)-product-dense.

Each stage records a specific last-coordinate witness whose selected
source index lies strictly below the current test index. The tower
supports a single strictly increasing (thus unbounded) sequence of
source indices and decreasing cone-dense last-coordinate sets.

The subsequent sparse finite Halpern--Läuchli application is separate.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Increasing the input density threshold preserves section-goodness.
This is the monotonicity required to choose each tower index above its
distinguished sample's actual selected source index. -/
theorem heterogeneousSectionsGoodAt_mono_input
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (k : ℕ) {m n : ℕ} (hmn : m ≤ n)
    (Y : Set U)
    (hgood : HeterogeneousSectionsGoodAt P Q k m Y) :
    HeterogeneousSectionsGoodAt P Q k n Y := by
  apply (heterogeneousSectionsGoodAt_iff P Q k n Y).2
  intro y hy hbad
  have hbadm : HeterogeneousBadSectionAt P Q k m y :=
    heterogeneousBadSectionAt_of_le P Q k hmn y hbad
  exact ((heterogeneousSectionsGoodAt_iff P Q k m Y).1
    hgood y hy) hbadm

/-- One stage, with a sample whose source index is below the matrix
density index. The last-coordinate factor T can have arbitrarily
varying finite local branching. -/
structure HeterogeneousLemma316TowerState
    (T : StrongSubtree U) where
  n : ℕ
  X : Set U
  inside : X ⊆ T.carrier
  dense : HeterogeneousSomewhereConeDense T X
  sample : U
  sample_mem : sample ∈ X
  sampleIndex : ℕ
  sample_source : sample ∈ T.sourceLevel sampleIndex
  sample_below : sampleIndex < n

/-- Initial tower state in the genuine T-cone above t, retaining
t itself as the distinguished sample and starting at a test
source index above both its source level and the requested target. -/
noncomputable def initialHeterogeneousLemma316TowerState
    (T : StrongSubtree U)
    (k r : ℕ) (t : U) (ht : t ∈ T.sourceLevel r) :
    HeterogeneousLemma316TowerState T where
  n := max k (r + 1)
  X := {z | z ∈ T.carrier ∧ t ≤ z}
  inside := fun _ hz => hz.1
  dense := by
    refine ⟨t, ht.1, ?_⟩
    intro z hz htz
    exact ⟨z, ⟨hz, htz⟩, le_rfl⟩
  sample := t
  sample_mem := ⟨ht.1, le_rfl⟩
  sampleIndex := r
  sample_source := ht
  sample_below := by omega

/-- One Lemma 3.15 tower step, including the corrected strict
source-index growth and an explicitly source-bounded sample. -/
structure HeterogeneousLemma316TowerStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (S : HeterogeneousLemma316TowerState (P (Fin.last d))) where
  next : HeterogeneousLemma316TowerState (P (Fin.last d))
  n_lt : S.n < next.n
  X_subset : next.X ⊆ S.X
  good : HeterogeneousSectionsGoodAt
    P (heterogeneousTailNormalize P Q) S.n next.n next.X

/-- The next tower step is obtained *only* from the proved
heterogeneous Lemma 3.15 and elementary source-level ancestry. -/
theorem exists_nextHeterogeneousLemma316TowerStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (S : HeterogeneousLemma316TowerState (P (Fin.last d))) :
    Nonempty (HeterogeneousLemma316TowerStep P Q S) := by
  classical
  let T : StrongSubtree U := P (Fin.last d)
  obtain ⟨m, Y, hYS, hYdense, hgood⟩ :=
    heterogeneousLemma315_tailNormalize
      P Q hd hstab hno S.n S.X S.inside S.dense
  have hYinside : Y ⊆ T.carrier :=
    fun _ hy => S.inside (hYS hy)
  obtain ⟨root, hroot, hdenseRoot⟩ := hYdense
  obtain ⟨y, hyY, _⟩ :=
    hdenseRoot root hroot le_rfl
  have hyCarrier : y ∈ T.carrier := hYinside hyY
  obtain ⟨q, hq⟩ := T.carrier_levels y hyCarrier
  let n : ℕ := max (max (S.n + 1) m) (q + 1)
  have hSm : S.n < n := by
    have h1 : S.n + 1 ≤ max (S.n + 1) m := Nat.le_max_left _ _
    have h2 : max (S.n + 1) m ≤ n := Nat.le_max_left _ _
    omega
  have hmn : m ≤ n :=
    (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  have hqn : q < n := by
    have hle : q + 1 ≤ n := Nat.le_max_right _ _
    omega
  let R : HeterogeneousLemma316TowerState T := {
    n := n
    X := Y
    inside := hYinside
    dense := ⟨root, hroot, hdenseRoot⟩
    sample := y
    sample_mem := hyY
    sampleIndex := q
    sample_source := ⟨hyCarrier, hq⟩
    sample_below := hqn
  }
  refine ⟨{
    next := R
    n_lt := hSm
    X_subset := hYS
    good := ?_
  }⟩
  exact heterogeneousSectionsGoodAt_mono_input
    P (heterogeneousTailNormalize P Q) S.n hmn Y hgood

/-- Choose a source-faithful heterogeneous tower step. -/
noncomputable def nextHeterogeneousLemma316TowerStep
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (S : HeterogeneousLemma316TowerState (P (Fin.last d))) :
    HeterogeneousLemma316TowerStep P Q S :=
  Classical.choice
    (exists_nextHeterogeneousLemma316TowerStep P Q hd hstab hno S)

/-- The recursively chosen family of actual-source-level states. -/
noncomputable def heterogeneousLemma316Tower
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r) :
    ℕ → HeterogeneousLemma316TowerState (P (Fin.last d))
  | 0 => initialHeterogeneousLemma316TowerState
      (P (Fin.last d)) k r t ht
  | p + 1 =>
      (nextHeterogeneousLemma316TowerStep
        P Q hd hstab hno
        (heterogeneousLemma316Tower P Q hd hstab hno
          k r t ht p)).next

/-- Consecutive selected tower source levels strictly increase. -/
theorem heterogeneousLemma316Tower_n_lt_succ
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r)
    (p : ℕ) :
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n <
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht (p + 1)).n := by
  change
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n <
    (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
      (heterogeneousLemma316Tower P Q hd hstab hno
        k r t ht p)).next.n
  exact (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p)).n_lt

/-- The chosen sequence of density source indices is strictly increasing. -/
theorem heterogeneousLemma316Tower_levels_strictMono
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r) :
    StrictMono (fun p =>
      (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n) := by
  apply strictMono_nat_of_lt_succ
  intro p
  exact heterogeneousLemma316Tower_n_lt_succ
    P Q hd hstab hno k r t ht p

/-- Any strictly increasing sequence of natural-numbered source
indices is unbounded; no extra branching assumption is needed. -/
theorem heterogeneousLemma316Tower_levels_unbounded
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r) :
    ∀ b : ℕ, ∃ p : ℕ,
      b ≤ (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n := by
  let f : ℕ → ℕ :=
    fun p => (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n
  have hf : StrictMono f :=
    heterogeneousLemma316Tower_levels_strictMono
      P Q hd hstab hno k r t ht
  have hdiag : ∀ p : ℕ, p ≤ f p := by
    intro p
    induction p with
    | zero => omega
    | succ p ih =>
        have hstep : f p < f (p + 1) :=
          hf (Nat.lt_succ_self p)
        omega
  intro b
  exact ⟨b, hdiag b⟩

/-- Consecutive tower cones are decreasing. -/
theorem heterogeneousLemma316Tower_X_succ_subset
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r)
    (p : ℕ) :
    (heterogeneousLemma316Tower P Q hd hstab hno
      k r t ht (p + 1)).X ⊆
    (heterogeneousLemma316Tower P Q hd hstab hno
      k r t ht p).X := by
  change
    (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
      (heterogeneousLemma316Tower P Q hd hstab hno
        k r t ht p)).next.X ⊆
    (heterogeneousLemma316Tower P Q hd hstab hno
      k r t ht p).X
  exact (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p)).X_subset

/-- Arbitrary later tower cones lie inside their earlier stages. -/
theorem heterogeneousLemma316Tower_X_antitone
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r)
    {p q : ℕ} (hpq : p ≤ q) :
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht q).X ⊆
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).X := by
  induction q generalizing p with
  | zero =>
      have hp : p = 0 := Nat.eq_zero_of_le_zero hpq
      subst p
      exact fun _ hx => hx
  | succ q ih =>
      rcases Nat.eq_or_lt_of_le hpq with hp | hp
      · subst p
        exact fun _ hx => hx
      · have hpq' : p ≤ q := Nat.le_of_lt_succ hp
        exact (heterogeneousLemma316Tower_X_succ_subset
          P Q hd hstab hno k r t ht q).trans (ih hpq')

/-- Adjacent tower steps satisfy the exact uniform section-goodness
property required by the heterogeneous Lemma 3.16 argument. -/
theorem heterogeneousLemma316Tower_good
    (P : Fin (d + 1) → StrongSubtree U)
    (Q : Set (Fin (d + 1) → U))
    (hd : 0 < d)
    (hstab : HeterogeneousStabilized P Q)
    (hno : ¬ HeterogeneousContainsSomewhereDense P Qᶜ)
    (k r : ℕ) (t : U)
    (ht : t ∈ (P (Fin.last d)).sourceLevel r)
    (p : ℕ) :
    HeterogeneousSectionsGoodAt P (heterogeneousTailNormalize P Q)
      (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n
      (heterogeneousLemma316Tower P Q hd hstab hno k r t ht (p + 1)).n
      (heterogeneousLemma316Tower P Q hd hstab hno k r t ht (p + 1)).X := by
  change
    HeterogeneousSectionsGoodAt P (heterogeneousTailNormalize P Q)
      (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p).n
      (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
        (heterogeneousLemma316Tower P Q hd hstab hno
          k r t ht p)).next.n
      (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
        (heterogeneousLemma316Tower P Q hd hstab hno
          k r t ht p)).next.X
  exact (nextHeterogeneousLemma316TowerStep P Q hd hstab hno
    (heterogeneousLemma316Tower P Q hd hstab hno k r t ht p)).good

end GeneralTree
end Milliken
