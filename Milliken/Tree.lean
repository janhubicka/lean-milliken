import Mathlib

/-!
# Strong embeddings of finitely branching homogeneous trees

We use the full tree `List ι` over a finite alphabet.  A strong subtree is
represented by its canonical strong embedding.  This is the standard
homogeneous-tree presentation of Milliken's theorem and is the first concrete
case needed by the Chapter 6 argument.

The level map is kept existential in `StrongEmbedding`.  Consequently two
strong embeddings with the same node map are definitionally the same
mathematical object (all remaining fields are propositions), which makes the
later approximation space substantially cleaner.
-/

namespace Milliken

universe u

abbrev Node (ι : Type u) := List ι

def child (s : Node ι) (i : ι) : Node ι :=
  s ++ [i]

/-- A strong self-embedding of the full finitely branching tree `ι^{<ω}`.

The branch-label clause is Todorčević's condition (str2) in embedding form:
the image of the `i`-successor of `s` extends the `i`-successor of the
image of `s`.  The witness `levels` says that all nodes on one source level
land on a common target level. -/
structure StrongEmbedding (ι : Type u) where
  toFun : Node ι → Node ι
  map_nil : toFun [] = []
  injective : Function.Injective toFun
  prefix_mono :
    ∀ {s t : Node ι}, s.IsPrefix t → (toFun s).IsPrefix (toFun t)
  branch :
    ∀ (s : Node ι) (i : ι), (child (toFun s) i).IsPrefix (toFun (child s i))
  level_witness :
    ∃ levels : ℕ → ℕ,
      StrictMono levels ∧ levels 0 = 0 ∧
        ∀ s : Node ι, (toFun s).length = levels s.length

namespace StrongEmbedding

variable {ι : Type u}

@[ext]
theorem ext {F G : StrongEmbedding ι}
    (h : ∀ s, F.toFun s = G.toFun s) : F = G := by
  cases F
  cases G
  congr
  funext s
  exact h s

/-- The identity strong embedding. -/
def id : StrongEmbedding ι where
  toFun := fun s => s
  map_nil := rfl
  injective := Function.injective_id
  prefix_mono := fun h => h
  branch := by
    intro s i
    simp [child]
  level_witness := by
    refine ⟨fun n => n, strictMono_id, rfl, ?_⟩
    intro s
    rfl

/-- Composition of strong embeddings.  The level map of the composite is the
composition of the two level maps. -/
def comp (F G : StrongEmbedding ι) : StrongEmbedding ι where
  toFun := fun s => F.toFun (G.toFun s)
  map_nil := by simp [G.map_nil, F.map_nil]
  injective := F.injective.comp G.injective
  prefix_mono := by
    intro s t hst
    exact F.prefix_mono (G.prefix_mono hst)
  branch := by
    intro s i
    exact (F.branch (G.toFun s) i).trans
      (F.prefix_mono (G.branch s i))
  level_witness := by
    rcases F.level_witness with ⟨f, hf, hf0, hF⟩
    rcases G.level_witness with ⟨g, hg, hg0, hG⟩
    refine ⟨fun n => f (g n), hf.comp hg, ?_, ?_⟩
    · simp [hg0, hf0]
    · intro s
      rw [hF, hG]

@[simp] theorem id_toFun (s : Node ι) :
    (id : StrongEmbedding ι).toFun s = s := rfl

@[simp] theorem comp_toFun (F G : StrongEmbedding ι) (s : Node ι) :
    (comp F G).toFun s = F.toFun (G.toFun s) := rfl

@[simp] theorem comp_id (F : StrongEmbedding ι) :
    comp F id = F := by
  ext s
  simp

@[simp] theorem id_comp (F : StrongEmbedding ι) :
    comp id F = F := by
  ext s
  simp

theorem comp_assoc (F G H : StrongEmbedding ι) :
    comp (comp F G) H = comp F (comp G H) := by
  ext s
  rfl

/-- The set of nodes of the strong subtree represented by an embedding. -/
def range (F : StrongEmbedding ι) : Set (Node ι) :=
  Set.range F.toFun

end StrongEmbedding

end Milliken
