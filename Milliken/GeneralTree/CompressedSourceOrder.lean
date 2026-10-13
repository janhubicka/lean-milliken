import Milliken.GeneralTree.CompressedSourceFrame

/-!
# The underlying order of the full selected-source compression

The compression of a strong tree S along strictly increasing selected
indices f retains *all* nodes of S.sourceLevel (f n). Its node type is
a disjoint union of these actual finite levels, with the ancestry
order pulled back from the original ambient tree.

The source index is part of each node, but the underlying U-node
determines that index uniquely. Consequently the ancestry relation
is a genuine partial order, with the original root as bottom.

Every compressed node has a unique ancestor at each preceding
compressed rank, and ancestry forces monotonicity of those ranks.
This is geometry of the **full compressed tree**; unlike strong
thinning, it does not throw away branches at skipped levels.

No Ramsey assumption or global bound on local branching is used.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

namespace CompressedSourceSelection

variable (S : StrongSubtree U) (f : CompressedSourceSelection)

/-- An indexed node of the full compression.

This is deliberately a new structure, not a Sigma abbreviation:
Mathlib equips Sigma types with a disjoint-fibre order, which
does not compare nodes at distinct compressed source indices.
A new structure allows us to install the actual ancestry order
without conflicting order instances. -/
structure Node where
  fst : ℕ
  snd : NodeAt S f fst

/-- Recover its original ambient node. -/
def nodeValue (x : Node S f) : U := x.2.1

/-- Its compressed source index. -/
def nodeIndex (x : Node S f) : ℕ := x.1

theorem nodeValue_injective :
    Function.Injective (nodeValue S f) := by
  intro a b hab
  rcases a with ⟨n, x⟩
  rcases b with ⟨m, y⟩
  change x.1 = y.1 at hab
  have hlevels :
      S.levels (f.indices n) = S.levels (f.indices m) := by
    calc
      S.levels (f.indices n) = U.level x.1 := x.2.2.symm
      _ = U.level y.1 := congrArg U.level hab
      _ = S.levels (f.indices m) := y.2.2
  have hnm : n = m :=
    f.strictMono.injective (S.levels_strictMono.injective hlevels)
  subst m
  have hxy : x = y := Subtype.ext hab
  subst y
  rfl

/-- The compressed order is exactly the original ancestor order. -/
instance nodePartialOrder : PartialOrder (Node S f) :=
  PartialOrder.lift (nodeValue S f) (nodeValue_injective S f)

theorem node_le_iff (a b : Node S f) :
    a ≤ b ↔ nodeValue S f a ≤ nodeValue S f b := Iff.rfl

/-- The original source-zero root is the unique compressed root. -/
def nodeRoot : Node S f := ⟨0, root S f⟩

instance nodeOrderBot : OrderBot (Node S f) where
  bot := nodeRoot S f
  bot_le := by
    intro x
    apply (node_le_iff S f _ _).mpr
    exact root_below S f x.1 x.2

@[simp] theorem nodeValue_bot :
    nodeValue S f (⊥ : Node S f) = S.root := by
  rfl

@[simp] theorem nodeIndex_bot :
    nodeIndex S f (⊥ : Node S f) = 0 := rfl

/-- Any ancestor has no greater compressed index than its descendant. -/
theorem nodeIndex_mono {a b : Node S f} (hab : a ≤ b) :
    a.1 ≤ b.1 := by
  have hvalue :
      U.level a.2.1 ≤ U.level b.2.1 :=
    U.level_mono ((node_le_iff S f a b).mp hab)
  have hlevel :
      S.levels (f.indices a.1) ≤ S.levels (f.indices b.1) := by
    calc
      S.levels (f.indices a.1) = U.level a.2.1 := a.2.2.2.symm
      _ ≤ U.level b.2.1 := hvalue
      _ = S.levels (f.indices b.1) := b.2.2.2
  by_contra hnot
  have hba : b.1 < a.1 := Nat.lt_of_not_ge hnot
  have hstrict :
      S.levels (f.indices b.1) < S.levels (f.indices a.1) :=
    S.levels_strictMono (f.strictMono hba)
  omega

/-- Comparability at the same compressed index forces equality. -/
theorem node_eq_of_le_index_eq
    {a b : Node S f} (hab : a ≤ b) (hrank : a.1 = b.1) :
    a = b := by
  have hval :
      nodeValue S f a = nodeValue S f b := by
    apply U.eq_of_le_of_level_eq
      ((node_le_iff S f a b).mp hab)
    change U.level a.2.1 = U.level b.2.1
    calc
      U.level a.2.1 = S.levels (f.indices a.1) := a.2.2.2
      _ = S.levels (f.indices b.1) := by rw [hrank]
      _ = U.level b.2.1 := b.2.2.2.symm
  exact (nodeValue_injective S f) hval

/-- The original unique selected-level ancestor, now as a node of
the fully compressed tree. -/
noncomputable def nodeAncestor {n m : ℕ} (hnm : n ≤ m)
    (z : Node S f) (hm : z.1 = m) : Node S f :=
  ⟨n, truncate S f hnm (hm ▸ z.2)⟩

theorem nodeAncestor_index {n m : ℕ} (hnm : n ≤ m)
    (z : Node S f) (hm : z.1 = m) :
    (nodeAncestor S f hnm z hm).1 = n := rfl

theorem nodeAncestor_le {n m : ℕ} (hnm : n ≤ m)
    (z : Node S f) (hm : z.1 = m) :
    nodeAncestor S f hnm z hm ≤ z := by
  apply (node_le_iff S f _ _).mpr
  change (truncate S f hnm (hm ▸ z.2)).1 ≤ z.2.1
  cases hm
  exact truncate_below S f hnm z.2

/-- At a fixed earlier compressed rank, the ancestor below z is unique. -/
theorem nodeAncestor_unique
    {n m : ℕ} (hnm : n ≤ m)
    (z : Node S f) (hm : z.1 = m)
    (x : Node S f) (hxn : x.1 = n) (hxz : x ≤ z) :
    x = nodeAncestor S f hnm z hm := by
  apply nodeValue_injective S f
  have hxlevel : U.level x.2.1 =
      U.level (nodeAncestor S f hnm z hm).2.1 := by
    calc
      U.level x.2.1 = S.levels (f.indices x.1) := x.2.2.2
      _ = S.levels (f.indices n) := by rw [hxn]
      _ = U.level (nodeAncestor S f hnm z hm).2.1 :=
        (nodeAncestor S f hnm z hm).2.2.2.symm
  exact U.eq_of_common_descendant_of_level_eq
    ((node_le_iff S f _ _).mp hxz)
    ((node_le_iff S f _ _).mp (nodeAncestor_le S f hnm z hm))
    hxlevel

/-- There is exactly one compressed ancestor at each prior rank. -/
theorem existsUnique_nodeAncestor
    (z : Node S f) (n : ℕ) (hn : n ≤ z.1) :
    ∃! x : Node S f, x.1 = n ∧ x ≤ z := by
  let x : Node S f := nodeAncestor S f hn z rfl
  refine ⟨x, ⟨rfl, nodeAncestor_le S f hn z rfl⟩, ?_⟩
  intro y hy
  exact nodeAncestor_unique S f hn z rfl y hy.1 hy.2

/-- Every compressed index has a finite, nonempty full level. -/
theorem node_level_finite (n : ℕ) :
    ({x : Node S f | x.1 = n} : Set (Node S f)).Finite := by
  letI : Finite (NodeAt S f n) := nodeAtFinite S f n
  have hfin : (Set.range (fun x : NodeAt S f n => (⟨n, x⟩ : Node S f))).Finite :=
    Set.finite_range _
  apply hfin.subset
  intro x hx
  rcases x with ⟨m, y⟩
  dsimp at hx
  subst m
  exact ⟨y, rfl⟩

theorem node_level_nonempty (n : ℕ) :
    ({x : Node S f | x.1 = n} : Set (Node S f)).Nonempty := by
  obtain ⟨x⟩ := nodeAtNonempty S f n
  exact ⟨⟨n, x⟩, rfl⟩

end CompressedSourceSelection
end GeneralTree
end Milliken
