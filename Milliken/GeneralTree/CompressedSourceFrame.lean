import Milliken.GeneralTree.HeterogeneousTruncation
import Milliken.GeneralTree.ThinningStrong

/-!
# Full selected-source-level compression of a strong tree

For an actual strong tree S and any strictly increasing source-index
sequence f with f(0)=0, the compressed tree at rank n consists of
**all** nodes of S.sourceLevel (f n), not the single chosen node in
each ambient child cone of a strong thinning.

An immediate compressed child of x is ANY node on the next selected
source level extending x. These sets are finite and nonempty even if
the degrees of S are unbounded and vary by node. Every deeper node
has a unique selected-source ancestor and passes through a next
compressed child.

This is the correct geometric structure required by Todorčević
Remark 3.8. It is deliberately *not* identified with a strong
subtree of the old ambient tree. The remaining step is to bundle
the union of these levels as a fresh RootedTree/AmbientTree and
transfer the reduced HDHL theorem along that compression.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- A chosen strictly increasing set of source indices, retaining
the original root at compressed level zero. -/
structure CompressedSourceSelection where
  indices : ℕ → ℕ
  zero : indices 0 = 0
  strictMono : StrictMono indices

namespace CompressedSourceSelection

variable (S : StrongSubtree U)
variable (f : CompressedSourceSelection)

/-- Every node of the actual full selected source level. -/
abbrev NodeAt (n : ℕ) :=
  {x : U // x ∈ S.sourceLevel (f.indices n)}

instance nodeAtFinite (n : ℕ) :
    Finite (NodeAt S f n) :=
  ((S.sourceLevel_finite (f.indices n)).to_subtype)

instance nodeAtNonempty (n : ℕ) :
    Nonempty (NodeAt S f n) := by
  obtain ⟨x, hx⟩ := S.sourceLevel_nonempty (f.indices n)
  exact ⟨⟨x, hx⟩⟩

/-- Original strong-tree root as the sole compressed source-zero node. -/
def root : NodeAt S f 0 :=
  ⟨S.root, by
    rw [f.zero]
    exact ⟨S.root_mem, S.root_level⟩⟩

/-- The **entire** immediate successor set in the compressed tree,
not one representative per old ambient child cone. -/
abbrev Child {n : ℕ} (x : NodeAt S f n) :=
  {y : NodeAt S f (n + 1) // x.1 ≤ y.1}

instance childFinite {n : ℕ} (x : NodeAt S f n) :
    Finite (Child S f x) := by
  letI : Finite (NodeAt S f (n + 1)) :=
    nodeAtFinite S f (n + 1)
  apply Finite.of_injective
    (fun y : Child S f x => y.1)
  intro y z h
  exact Subtype.ext h

/-- Every node has a next compressed child, by arbitrary-source-level
descendant existence in the actual original strong tree. -/
theorem child_nonempty {n : ℕ} (x : NodeAt S f n) :
    Nonempty (Child S f x) := by
  obtain ⟨y, hy, hxy⟩ :=
    S.exists_sourceLevel_descendant
      (f.strictMono.monotone (Nat.le_succ n)) x.2
  exact ⟨⟨⟨y, hy⟩, hxy⟩⟩

/-- Canonical retained ancestor at an earlier selected source index. -/
noncomputable def truncate
    {m n : ℕ} (hmn : m ≤ n)
    (z : NodeAt S f n) : NodeAt S f m :=
  ⟨S.sourceAncestorAt (f.strictMono.monotone hmn) z.2,
    (S.sourceAncestorAt_spec
      (f.strictMono.monotone hmn) z.2).1⟩

theorem truncate_below
    {m n : ℕ} (hmn : m ≤ n)
    (z : NodeAt S f n) :
    (truncate S f hmn z).1 ≤ z.1 :=
  (S.sourceAncestorAt_spec
    (f.strictMono.monotone hmn) z.2).2

/-- Uniqueness of a source-level predecessor: an earlier selected
node below a later one is exactly its compressed truncation. -/
theorem truncate_eq_of_le
    {m n : ℕ} (hmn : m ≤ n)
    (x : NodeAt S f m) (z : NodeAt S f n)
    (hxz : x.1 ≤ z.1) :
    truncate S f hmn z = x := by
  apply Subtype.ext
  have hanc :=
    S.sourceAncestorAt_spec (f.strictMono.monotone hmn) z.2
  have hlevels : U.level x.1 =
      U.level (truncate S f hmn z).1 :=
    x.2.2.trans hanc.1.2.symm
  exact (U.eq_of_common_descendant_of_level_eq
    hxz (truncate_below S f hmn z) hlevels).symm

/-- Every selected-level extension factors through a genuine
immediate child of the compressed tree. -/
theorem exists_child_below
    {n q : ℕ} (hnq : n < q)
    (x : NodeAt S f n) (z : NodeAt S f q)
    (hxz : x.1 ≤ z.1) :
    ∃ y : Child S f x, y.1.1 ≤ z.1 := by
  have hnq' : n + 1 ≤ q := Nat.succ_le_of_lt hnq
  let y0 : NodeAt S f (n + 1) :=
    truncate S f hnq' z
  have hyz : y0.1 ≤ z.1 :=
    truncate_below S f hnq' z
  have hxy : x.1 ≤ y0.1 := by
    rcases le_total_of_directed hxz hyz with hyx | hxy
    · have hlevels : S.levels (f.indices (n + 1)) ≤
          S.levels (f.indices n) := by
        calc
          S.levels (f.indices (n + 1)) =
              U.level y0.1 := y0.2.2.symm
          _ ≤ U.level x.1 := U.level_mono hyx
          _ = S.levels (f.indices n) := x.2.2
      have hstrict : S.levels (f.indices n) <
          S.levels (f.indices (n + 1)) :=
        S.levels_strictMono
          (f.strictMono (Nat.lt_succ_self n))
      omega
    · exact hxy
  exact ⟨⟨y0, hxy⟩, hyz⟩

/-- Roots of all compressed source levels descend from the original
strong-tree root, including after arbitrary nonuniform gaps. -/
theorem root_below
    (n : ℕ) (x : NodeAt S f n) :
    (root S f).1 ≤ x.1 :=
  S.root_below x.1 x.2.1

/-- In contrast to strong thinning, the compressed level retains
the full original selected source-level set exactly. -/
theorem nodeAt_carrier_eq
    (n : ℕ) :
    {x : U | ∃ v : NodeAt S f n, v.1 = x} =
      S.sourceLevel (f.indices n) := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact v.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

end CompressedSourceSelection
end GeneralTree
end Milliken
