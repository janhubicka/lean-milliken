import Milliken.DepthBoundary
import Milliken.GraftRamsey

/-!
# Boundary continuations for amalgamation

Let `a = r_n(B ∘ H)` have depth `d` in `B`, with `n > 0`.
Minimality of depth puts every image of source level `n-1` under `H`
on level `d-1`.

For a new source node `r` on level `n`, write it as its parent followed
by one branch label.  The corresponding depth boundary node is the same
branch label above the image of the parent.  Strongness makes this boundary
node a prefix of `H(r)`.  Rebasing the cone of `H` above `r` at that
boundary gives the continuation that will be grafted into `B`.
-/

namespace Milliken
namespace AmalgamationBoundary

universe u

variable {ι : Type u}

/-- A positive-level node is nonempty. -/
theorem levelNode_ne_nil {n : ℕ} (hn : 0 < n)
    (r : LevelNode ι n) :
    r.1 ≠ [] := by
  intro hr
  have hlen : r.1.length = 0 := by
    rw [hr]
    rfl
  omega

/-- Parent of a node on positive level `n`. -/
def parentNode {n : ℕ} (hn : 0 < n)
    (r : LevelNode ι n) :
    LevelNode ι (n - 1) :=
  ⟨r.1.dropLast, by
    rw [List.length_dropLast, r.2]
    omega⟩

/-- Last branch label of a positive-level node. -/
def lastLabel {n : ℕ} (hn : 0 < n)
    (r : LevelNode ι n) : ι :=
  r.1.getLast (levelNode_ne_nil hn r)

/-- Reconstruct a positive-level node from its parent and last label. -/
theorem parent_child {n : ℕ} (hn : 0 < n)
    (r : LevelNode ι n) :
    child (parentNode hn r).1 (lastLabel hn r) = r.1 := by
  simpa [child, parentNode, lastLabel] using
    (List.dropLast_append_getLast (levelNode_ne_nil hn r))

/-- The depth-`d` boundary node corresponding to a new source node. -/
def frontierNode {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n) :
    LevelNode ι d :=
  ⟨child (H.toFun (parentNode hn r).1) (lastLabel hn r), by
    simp [child, htop (parentNode hn r)]
    omega⟩

/-- The frontier node really is below the image of the new source node. -/
theorem frontier_prefix_image {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n) :
    (frontierNode hn hd H htop r).1.IsPrefix (H.toFun r.1) := by
  change
    (child (H.toFun (parentNode hn r).1) (lastLabel hn r)).IsPrefix
      (H.toFun r.1)
  have h := H.branch (parentNode hn r).1 (lastLabel hn r)
  rw [parent_child hn r] at h
  exact h

/-- The continuation of `H` above a new source node, expressed relative to
the corresponding depth boundary node. -/
def continuation {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n) :
    StrongEmbedding ι :=
  let p := frontierNode hn hd H htop r
  StrongEmbedding.rebase
    (StrongEmbedding.cone H r.1) p.1
    (by
      change p.1.IsPrefix (H.toFun r.1)
      exact frontier_prefix_image hn hd H htop r)

/-- Grafting the rebased continuation back onto its boundary recovers the
original cone of `H`. -/
theorem continuation_reconstruct {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n) (s : Node ι) :
    (frontierNode hn hd H htop r).1 ++
        (continuation hn hd H htop r).toFun s =
      H.toFun (r.1 ++ s) := by
  let p := frontierNode hn hd H htop r
  have hp :
      p.1.IsPrefix ((StrongEmbedding.cone H r.1).toFun []) := by
    change p.1.IsPrefix (H.toFun r.1)
    exact frontier_prefix_image hn hd H htop r
  have h := StrongEmbedding.prefix_append_rebase
    (StrongEmbedding.cone H r.1) hp s
  simpa [p, continuation] using h

/-- All boundary continuations have the same target length on each source
level. -/
theorem continuation_length {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n)
    (levels : ℕ → ℕ)
    (hlevels :
      ∀ s : Node ι, (H.toFun s).length = levels s.length)
    (s : Node ι) :
    ((continuation hn hd H htop r).toFun s).length =
      levels (n + s.length) - d := by
  have h := congrArg List.length
    (continuation_reconstruct hn hd H htop r s)
  rw [List.length_append, (frontierNode hn hd H htop r).2,
      hlevels, List.length_append, r.2] at h
  omega

/-- The family of continuations has one common level set. -/
theorem continuations_commonLevels
    [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1) :
    ∃ levels : ℕ → ℕ,
      StrictMono levels ∧
        ∀ (r : LevelNode ι n) (s : Node ι),
          ((continuation hn hd H htop r).toFun s).length =
            levels s.length := by
  rcases H.level_witness with ⟨levels, hmono, hlevels⟩
  let r0 : LevelNode ι n :=
    ⟨rayNode (ι := ι) n, rayNode_length n⟩
  have hfront :
      (frontierNode hn hd H htop r0).1.IsPrefix
        (H.toFun r0.1) :=
    frontier_prefix_image hn hd H htop r0
  have hdlev : d ≤ levels n := by
    have hlen := hfront.length_le
    rw [(frontierNode hn hd H htop r0).2,
        hlevels, r0.2] at hlen
    exact hlen
  refine ⟨fun k => levels (n + k) - d, ?_, ?_⟩
  · intro a b hab
    have hda : d ≤ levels (n + a) :=
      hdlev.trans (hmono.monotone (by omega))
    exact Nat.sub_lt_sub_right hda
      (hmono (Nat.add_lt_add_left hab n))
  · intro r s
    exact continuation_length hn hd H htop r levels hlevels s

end AmalgamationBoundary
end Milliken
