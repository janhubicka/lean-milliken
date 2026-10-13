import Milliken.GeneralTree.HeterogeneousWedgeHeights
import Milliken.GeneralTree.ConeStrong
import Milliken.GeneralTree.Identity

/-!
# Heterogeneous components via the checked strong-cone constructor

The homogeneous and general-tree library already proves that any source
node of a strong tree determines a genuine strong successor cone.
We use exactly that constructor, instead of reproving (str1)–(str2)
for each component of the newly rooted heterogeneous forest.

The wedge's complete i-th component is the cone rooted at the tagged
i-th local root, viewed inside the *identity strong subtree* of the
new ambient. The resulting coordinate families are synchronized
on the single ambient level sequence n ↦ n+1.

This construction does not discard any node of any compressed
coordinate tree. No global bound on local degree is needed.
-/

namespace Milliken
namespace GeneralTree

variable {d : ℕ}

namespace WedgeNode

variable (T : Fin d → AmbientTree) (hd : 0 < d)

/-- The tagged root of a coordinate is a genuine source-one node
in the identity strong subtree of the common-root ambient. -/
theorem component_root_sourceLevel (i : Fin d) :
    embed T i (⊥ : T i) ∈
      (identityStrongSubtree (ambientTree T hd)).sourceLevel 1 := by
  constructor
  · exact Set.mem_univ _
  · change (ambientTree T hd).level (embed T i (⊥ : T i)) = 1
    rw [ambient_level_embed T hd i (⊥ : T i)]
    rw [(T i).level_root]

/-- The entire i-th component, obtained from the **checked**
general-tree successor-cone constructor, rather than imposing an
unproved new strong-tree structure. -/
noncomputable def componentStrong (i : Fin d) :
    StrongSubtree (ambientTree T hd) :=
  (identityStrongSubtree (ambientTree T hd)).coneStrong
    1 (embed T i (⊥ : T i)) (component_root_sourceLevel T hd i)

/-- Every component uses exactly the same selected ambient heights. -/
theorem componentStrong_levels (i : Fin d) :
    (componentStrong T hd i).levels = (fun n : ℕ => n + 1) := by
  funext n
  change 1 + n = n + 1
  omega

/-- Each component is rooted at its original tagged root. -/
@[simp] theorem componentStrong_root (i : Fin d) :
    (componentStrong T hd i).root = embed T i (⊥ : T i) := rfl

/-- The carrier is precisely the cone above the tagged root.
The original identity carrier is the entire ambient. -/
theorem mem_componentStrong_iff (i : Fin d) (z : WedgeNode T) :
    z ∈ (componentStrong T hd i).carrier ↔
      embed T i (⊥ : T i) ≤ z := by
  change (z ∈ (Set.univ : Set (WedgeNode T)) ∧
    embed T i (⊥ : T i) ≤ z) ↔ _
  simp

/-- Every original node in component i is retained, at every
source level, without applying any strong thinning. -/
theorem embed_mem_componentStrong (i : Fin d) (x : T i) :
    embed T i x ∈ (componentStrong T hd i).carrier := by
  rw [mem_componentStrong_iff]
  exact (embed_le_embed_iff T i (⊥ : T i) x).mpr bot_le

/-- The order cone above the i-th root contains no foreign nodes.
This supplies the inverse transport back to the dependent coordinate
node type without a type-unsafe Sigma coercion. -/
theorem exists_embed_of_mem_componentStrong
    (i : Fin d) (z : WedgeNode T)
    (hz : z ∈ (componentStrong T hd i).carrier) :
    ∃ x : T i, embed T i x = z := by
  have hzroot : embed T i (⊥ : T i) ≤ z :=
    (mem_componentStrong_iff T hd i z).mp hz
  rcases z with _ | ⟨j, y⟩
  · exact False.elim (WithBot.not_coe_le_bot _ hzroot)
  · change embed T i (⊥ : T i) ≤ embed T j y at hzroot
    have hij : i = j :=
      (Sigma.le_def.mp (WithBot.coe_le_coe.mp hzroot)).1
    subst j
    exact ⟨y, rfl⟩

/-- Exact correspondence of source levels: no coordinate nodes are
lost when a full compressed component is installed in the common
ambient as a genuine strong subtree. -/
theorem mem_componentStrong_sourceLevel_iff
    (i : Fin d) (n : ℕ) (z : WedgeNode T) :
    z ∈ (componentStrong T hd i).sourceLevel n ↔
      ∃ x : T i, (T i).level x = n ∧ embed T i x = z := by
  constructor
  · intro hz
    obtain ⟨x, hx⟩ :=
      exists_embed_of_mem_componentStrong T hd i z hz.1
    refine ⟨x, ?_, hx⟩
    have hlev :
        (ambientTree T hd).level z = n + 1 := by
      have hl := hz.2
      rw [componentStrong_levels T hd i] at hl
      exact hl
    rw [← hx, ambient_level_embed T hd i x] at hlev
    omega
  · rintro ⟨x, hlev, rfl⟩
    constructor
    · exact embed_mem_componentStrong T hd i x
    · change (ambientTree T hd).level (embed T i x) =
        (componentStrong T hd i).levels n
      rw [componentStrong_levels, ambient_level_embed, hlev]

/-- Hence the synchronized family needed in the reduced heterogeneous
HDHL induction exists for any finite positive collection of ambients. -/
theorem componentStrong_synchronized :
    ∀ i : Fin d,
      (componentStrong T hd i).levels = (fun n : ℕ => n + 1) :=
  componentStrong_levels T hd

end WedgeNode
end GeneralTree
end Milliken
