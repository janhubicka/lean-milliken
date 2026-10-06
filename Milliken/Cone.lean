import Milliken.Tree

/-!
# Cones of homogeneous strong trees

If `T : StrongEmbedding ι` and `q` is a source node, the cone of `T`
above `T(q)` is again canonically a strong embedding: prepend `q` in the
source before applying `T`.

These cone embeddings are the coordinate trees used in Todorčević's proof of
Lemma 6.1.
-/

namespace Milliken

universe u
variable {ι : Type u}

namespace StrongEmbedding

/-- Prefixing a fixed word preserves the prefix relation. -/
theorem prefix_append_left (q : Node ι) {s t : Node ι}
    (h : s.IsPrefix t) :
    (q ++ s).IsPrefix (q ++ t) := by
  rcases h with ⟨r, rfl⟩
  refine ⟨r, ?_⟩
  simp [List.append_assoc]

/-- Prefixing a fixed word reflects the prefix relation. -/
theorem prefix_cancel_left (q : Node ι) {s t : Node ι}
    (h : (q ++ s).IsPrefix (q ++ t)) :
    s.IsPrefix t := by
  rcases h with ⟨r, hr⟩
  refine ⟨r, ?_⟩
  apply List.append_right_injective q
  simpa [List.append_assoc] using hr

/-- The cone of a strong embedding above the image of a source node. -/
def cone (T : StrongEmbedding ι) (q : Node ι) : StrongEmbedding ι where
  toFun := fun s => T.toFun (q ++ s)
  injective := by
    intro s t h
    exact List.append_right_injective q (T.injective h)
  prefix_mono := by
    intro s t h
    exact T.prefix_mono (prefix_append_left q h)
  prefix_reflect := by
    intro s t h
    exact prefix_cancel_left q (T.prefix_reflect h)
  branch := by
    intro s i
    have h := T.branch (q ++ s) i
    simpa [child, List.append_assoc] using h
  branch_reflect := by
    intro s t i h
    have h' := T.branch_reflect (q ++ s) (q ++ t) i h
    have h'' : (q ++ child s i).IsPrefix (q ++ t) := by
      simpa [child, List.append_assoc] using h'
    exact prefix_cancel_left q h''
  level_witness := by
    rcases T.level_witness with ⟨lev, hlev, hT⟩
    refine ⟨fun n => lev (q.length + n), ?_, ?_⟩
    · intro n m hnm
      exact hlev (Nat.add_lt_add_left hnm q.length)
    · intro s
      simpa [List.length_append, Nat.add_assoc] using hT (q ++ s)

@[simp] theorem cone_toFun (T : StrongEmbedding ι) (q s : Node ι) :
    (cone T q).toFun s = T.toFun (q ++ s) :=
  rfl

@[simp] theorem cone_nil_toFun (T : StrongEmbedding ι) (q : Node ι) :
    (cone T q).toFun [] = T.toFun q := by
  simp [cone]

/-- The cone range is exactly the part of `T` above `T(q)` whose source
preimage extends `q`. -/
theorem mem_range_cone_iff (T : StrongEmbedding ι) (q : Node ι)
    (x : Node ι) :
    x ∈ (cone T q).range ↔
      ∃ s : Node ι, x = T.toFun (q ++ s) := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩

end StrongEmbedding
end Milliken
