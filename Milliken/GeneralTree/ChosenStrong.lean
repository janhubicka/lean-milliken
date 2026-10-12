import Milliken.GeneralTree.ThinningStrong

/-!
# Chosen strong subtrees of arbitrary locally finite rooted trees

A strong-subtree fusion repeatedly selects, from each retained
node x, exactly one descendant in every *actual ambient immediate
child cone* of x, all on a prescribed common later source level.
The selected descendant can be chosen by a Ramsey matrix rather
than by the canonical thinning representative.

This file separates the unconditional geometry from the colouring:
a coherent family of such choices defines a genuine infinite
strong subtree, rooted at any retained node on the first prescribed
source level. Local branching may vary without any global bound.

The proof reuses the ancestry and uniqueness arguments of
\`ThinningStrong\`, replacing the canonical long-cone representative
by an arbitrary witness obeying just source-level membership and
the ambient child-cone condition.
-/

namespace Milliken
namespace GeneralTree
namespace StrongSubtree

variable {U : AmbientTree}

/-- A choice of one descendant in every ambient immediate child
cone at prescribed source indices f(k). The initial root may lie
at an arbitrary retained source level f(0), not necessarily at
the ambient root. These hypotheses are purely geometric. -/
structure LevelChoice
    (B : StrongSubtree U) (f : ℕ → ℕ) where
  root : U
  root_mem : root ∈ B.sourceLevel (f 0)
  next :
    (k : ℕ) → (x : U) →
      x ∈ B.sourceLevel (f k) → ChildIndex U x → U
  next_mem :
    ∀ (k : ℕ) (x : U)
      (hx : x ∈ B.sourceLevel (f k))
      (y : ChildIndex U x),
      next k x hx y ∈ B.sourceLevel (f (k + 1))
  next_above :
    ∀ (k : ℕ) (x : U)
      (hx : x ∈ B.sourceLevel (f k))
      (y : ChildIndex U x),
      (y : U) ≤ next k x hx y

variable {B : StrongSubtree U} {f : ℕ → ℕ}

/-- Dependent recursion generating the selected source levels,
with membership in B's prescribed source levels carried in
the type. -/
noncomputable def LevelChoice.levelData
    (C : LevelChoice B f) :
    (k : ℕ) → {s : Set U // s ⊆ B.sourceLevel (f k)} :=
  Nat.rec
    (motive := fun k => {s : Set U // s ⊆ B.sourceLevel (f k)})
    (⟨{C.root}, by
      intro z hz
      have heq : z = C.root := hz
      subst z
      exact C.root_mem⟩)
    (fun k prev =>
      ⟨{z : U |
          ∃ x : {v : U // v ∈ prev.1},
            ∃ y : ChildIndex U x.1,
              z = C.next k x.1 (prev.2 x.2) y},
        by
          intro z hz
          obtain ⟨x, y, rfl⟩ := hz
          exact C.next_mem k x.1 (prev.2 x.2) y⟩)

/-- Nodes at the kth selected source level of the fusion. -/
noncomputable def LevelChoice.level
    (C : LevelChoice B f) (k : ℕ) : Set U :=
  (C.levelData k).1

theorem LevelChoice.level_subset_sourceLevel
    (C : LevelChoice B f) (k : ℕ) :
    C.level k ⊆ B.sourceLevel (f k) :=
  (C.levelData k).2

theorem LevelChoice.level_zero
    (C : LevelChoice B f) :
    C.level 0 = {C.root} := rfl

theorem LevelChoice.level_succ_iff
    (C : LevelChoice B f) (k : ℕ) (z : U) :
    z ∈ C.level (k + 1) ↔
      ∃ x : {v : U // v ∈ C.level k},
        ∃ y : ChildIndex U x.1,
          z = C.next k x.1
            (C.level_subset_sourceLevel k x.2) y := by
  rfl

/-- The union of all recursively selected levels. -/
noncomputable def LevelChoice.carrier
    (C : LevelChoice B f) : Set U :=
  ⋃ k : ℕ, C.level k

theorem LevelChoice.carrier_levels
    (C : LevelChoice B f)
    {z : U} (hz : z ∈ C.carrier) :
    ∃ k : ℕ, U.level z = B.levels (f k) := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact ⟨k, (C.level_subset_sourceLevel k hk).2⟩

theorem LevelChoice.level_nonempty
    (C : LevelChoice B f)
    (k : ℕ) : (C.level k).Nonempty := by
  induction k with
  | zero =>
      rw [C.level_zero]
      exact ⟨C.root, rfl⟩
  | succ k ih =>
      obtain ⟨x, hx⟩ := ih
      obtain ⟨y, hxy⟩ := U.has_child x
      let xi : {v : U // v ∈ C.level k} := ⟨x, hx⟩
      let yi : ChildIndex U x := ⟨y, hxy⟩
      let z : U :=
        C.next k x (C.level_subset_sourceLevel k hx) yi
      refine ⟨z, ?_⟩
      exact (C.level_succ_iff k z).2 ⟨xi, yi, rfl⟩

theorem LevelChoice.level_root_below
    (C : LevelChoice B f)
    (k : ℕ) {z : U} (hz : z ∈ C.level k) :
    C.root ≤ z := by
  induction k generalizing z with
  | zero =>
      rw [C.level_zero] at hz
      have heq : z = C.root := hz
      subst z
      exact le_rfl
  | succ k ih =>
      obtain ⟨x, y, hzy⟩ :=
        (C.level_succ_iff k z).mp hz
      have hroot : C.root ≤ x.1 := ih x.2
      have hchild :
          (y : U) ≤ C.next k x.1
            (C.level_subset_sourceLevel k x.2) y :=
        C.next_above k x.1
          (C.level_subset_sourceLevel k x.2) y
      rw [hzy]
      exact hroot.trans (y.2.le.trans hchild)

theorem LevelChoice.level_predecessor_exists
    (C : LevelChoice B f)
    (k : ℕ) {z : U} (hz : z ∈ C.level (k + 1)) :
    ∃ x : U, x ∈ C.level k ∧
      U.level x = B.levels (f k) ∧ x ≤ z := by
  obtain ⟨x, y, hzy⟩ :=
    (C.level_succ_iff k z).mp hz
  have hxB : x.1 ∈ B.sourceLevel (f k) :=
    C.level_subset_sourceLevel k x.2
  refine ⟨x.1, x.2, hxB.2, ?_⟩
  rw [hzy]
  exact y.2.le.trans (C.next_above k x.1 hxB y)

theorem LevelChoice.carrier_subset
    (C : LevelChoice B f) :
    C.carrier ⊆ B.carrier := by
  intro z hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact (C.level_subset_sourceLevel k hk).1

theorem LevelChoice.root_mem_carrier
    (C : LevelChoice B f) :
    C.root ∈ C.carrier := by
  apply Set.mem_iUnion.mpr
  exact ⟨0, by rw [C.level_zero]; exact rfl⟩

theorem LevelChoice.carrier_root_below
    (C : LevelChoice B f)
    {z : U} (hz : z ∈ C.carrier) :
    C.root ≤ z := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact C.level_root_below k hk

/-- Distinct prescribed source indices have distinct ambient levels,
so the global carrier can be recovered at each selected index. -/
theorem LevelChoice.carrier_at_level
    (C : LevelChoice B f)
    (hf : StrictMono f)
    (k : ℕ) {z : U}
    (hz : z ∈ C.carrier)
    (hzk : U.level z = B.levels (f k)) :
    z ∈ C.level k := by
  obtain ⟨ell, hell⟩ := Set.mem_iUnion.mp hz
  have hlevels : B.levels (f ell) = B.levels (f k) :=
    (C.level_subset_sourceLevel ell hell).2.symm.trans hzk
  have hindex : ell = k :=
    hf.injective (B.levels_strictMono.injective hlevels)
  subst ell
  exact hell

theorem LevelChoice.carrier_predecessor_exists
    (C : LevelChoice B f)
    (hf : StrictMono f)
    (k : ℕ) {z : U}
    (hz : z ∈ C.carrier)
    (hzk : U.level z = B.levels (f (k + 1))) :
    ∃ x : U, x ∈ C.carrier ∧
      U.level x = B.levels (f k) ∧ x ≤ z := by
  have hzLevel : z ∈ C.level (k + 1) :=
    C.carrier_at_level hf (k + 1) hz hzk
  obtain ⟨x, hx, hxLevel, hxz⟩ :=
    C.level_predecessor_exists k hzLevel
  refine ⟨x, ?_, hxLevel, hxz⟩
  exact Set.mem_iUnion.mpr ⟨k, hx⟩

/-- The arbitrary chosen next level contains exactly one node
in each ambient child cone of any retained parent. -/
theorem LevelChoice.level_successor_unique
    (C : LevelChoice B f)
    (hf : StrictMono f)
    (k : ℕ) {x : U}
    (hx : x ∈ C.level k)
    (y : U) (hxy : x ⋖ y) :
    ∃! z : U, z ∈ C.level (k + 1) ∧ y ≤ z := by
  classical
  have hxB : x ∈ B.sourceLevel (f k) :=
    C.level_subset_sourceLevel k hx
  let yy : ChildIndex U x := ⟨y, hxy⟩
  let z : U := C.next k x hxB yy
  have hzIn : z ∈ C.level (k + 1) := by
    apply (C.level_succ_iff k z).2
    exact ⟨⟨x, hx⟩, yy, rfl⟩
  have hyz : y ≤ z :=
    C.next_above k x hxB yy
  refine ⟨z, ⟨hzIn, hyz⟩, ?_⟩
  intro w hw
  obtain ⟨⟨p, hp⟩, u, hwRep⟩ :=
    (C.level_succ_iff k w).mp hw.1
  have hpB : p ∈ B.sourceLevel (f k) :=
    C.level_subset_sourceLevel k hp
  have hpW : p ≤ w := by
    rw [hwRep]
    exact u.2.le.trans (C.next_above k p hpB u)
  have hxW : x ≤ w := hxy.le.trans hw.2
  have hrank : U.level p = U.level x :=
    hpB.2.trans hxB.2.symm
  have hpEq : p = x :=
    U.eq_of_common_descendant_of_level_eq hpW hxW hrank
  subst p
  have huW : (u : U) ≤ w := by
    rw [hwRep]
    exact C.next_above k x hpB u
  have hyu : y = (u : U) :=
    immediateChildren_eq_of_common_descendant U
      hxy u.2 hw.2 huW
  have huEq : u = yy := Subtype.ext hyu.symm
  subst u
  simpa only [z, yy] using hwRep

/-- Any coherent family of representatives produces a genuine
strong subtree inside its ambient input tree, with the selected
source levels prescribed by f and possibly deeper starting root. -/
noncomputable def LevelChoice.toStrongSubtree
    (C : LevelChoice B f)
    (hf : StrictMono f) : StrongSubtree U where
  carrier := C.carrier
  levels := fun k => B.levels (f k)
  levels_strictMono := B.levels_strictMono.comp hf
  root := C.root
  root_mem := C.root_mem_carrier
  root_level := C.root_mem.2
  root_below := by
    intro x hx
    exact C.carrier_root_below hx
  carrier_levels := by
    intro x hx
    exact C.carrier_levels hx
  predecessor_exists := by
    intro k z hz hlevel
    exact C.carrier_predecessor_exists hf k hz hlevel
  successor_unique := by
    intro k x hx hxlevel y hxy
    have hxStage : x ∈ C.level k :=
      C.carrier_at_level hf k hx hxlevel
    obtain ⟨z, hz, hunique⟩ :=
      C.level_successor_unique hf k hxStage y hxy
    refine ⟨z, ⟨?_, ?_, hz.2⟩, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨k + 1, hz.1⟩
    · exact (C.level_subset_sourceLevel (k + 1) hz.1).2
    · intro w hw
      have hwStage : w ∈ C.level (k + 1) :=
        C.carrier_at_level hf (k + 1) hw.1 hw.2.1
      exact hunique w ⟨hwStage, hw.2.2⟩

theorem LevelChoice.toStrongSubtree_refines
    (C : LevelChoice B f)
    (hf : StrictMono f) :
    (C.toStrongSubtree hf).Refines B :=
  C.carrier_subset

theorem LevelChoice.toStrongSubtree_levels
    (C : LevelChoice B f)
    (hf : StrictMono f) :
    (C.toStrongSubtree hf).levels = fun k => B.levels (f k) := rfl

theorem LevelChoice.toStrongSubtree_sourceLevel
    (C : LevelChoice B f)
    (hf : StrictMono f)
    (k : ℕ) :
    (C.toStrongSubtree hf).sourceLevel k = C.level k := by
  ext z
  constructor
  · rintro ⟨hz, hlevel⟩
    exact C.carrier_at_level hf k hz hlevel
  · intro hz
    refine ⟨?_, ?_⟩
    · exact Set.mem_iUnion.mpr ⟨k, hz⟩
    · exact (C.level_subset_sourceLevel k hz).2

end StrongSubtree
end GeneralTree
end Milliken
