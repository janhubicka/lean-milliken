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
  rw [r.2] at hlen
  omega

/-- Parent of a node on positive level `n`. -/
def parentNode {n : ℕ} (hn : 0 < n)
    (r : LevelNode ι n) :
    LevelNode ι (n - 1) :=
  ⟨r.1.dropLast, by
    rw [List.length_dropLast, r.2]⟩

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
      simpa using frontier_prefix_image hn hd H htop r)

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
    simpa using frontier_prefix_image hn hd H htop r
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


/-- A canonical fallback source node on level `n`. -/
noncomputable def defaultLevelNode [Nonempty ι] (n : ℕ) :
    LevelNode ι n :=
  ⟨rayNode (ι := ι) n, rayNode_length n⟩

/-- Choose a source-level-`n` node whose frontier is `p`, when one
exists; otherwise use a harmless fixed fallback. -/
noncomputable def assignedSource [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (p : LevelNode ι d) :
    LevelNode ι n := by
  classical
  exact if h : ∃ r : LevelNode ι n, frontierNode hn hd H htop r = p then
    Classical.choose h
  else
    defaultLevelNode n

theorem frontier_assignedSource [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (p : LevelNode ι d)
    (hp : ∃ r : LevelNode ι n, frontierNode hn hd H htop r = p) :
    frontierNode hn hd H htop
        (assignedSource hn hd H htop p) = p := by
  classical
  unfold assignedSource
  simp only [dif_pos hp]
  exact Classical.choose_spec hp

/-- Fill every depth boundary cone with one of the continuations of `H`.
On unused boundary nodes the choice is irrelevant. -/
noncomputable def spliceFamily [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (p : LevelNode ι d) :
    StrongEmbedding ι :=
  continuation hn hd H htop
    (assignedSource hn hd H htop p)

theorem spliceFamily_commonLevels [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1) :
    BoundaryGraft.HasCommonLevels (spliceFamily hn hd H htop) := by
  rcases continuations_commonLevels hn hd H htop with
    ⟨levels, hmono, hlevels⟩
  refine ⟨levels, hmono, ?_⟩
  intro p s
  exact hlevels (assignedSource hn hd H htop p) s

/-- On a used frontier, the splice family reconstructs a cone of `H`
(possibly the cone corresponding to another source node with the same
frontier). -/
theorem spliceFamily_reconstruct [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (p : LevelNode ι d)
    (hp : ∃ r : LevelNode ι n, frontierNode hn hd H htop r = p)
    (s : Node ι) :
    p.1 ++ (spliceFamily hn hd H htop p).toFun s =
      H.toFun ((assignedSource hn hd H htop p).1 ++ s) := by
  have hfront :=
    frontier_assignedSource hn hd H htop p hp
  have h := continuation_reconstruct hn hd H htop
    (assignedSource hn hd H htop p) s
  rw [hfront] at h
  exact h

/-- The full depth-boundary splice. -/
noncomputable def splice [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1) :
    StrongEmbedding ι :=
  BoundaryGraft.graft (spliceFamily hn hd H htop)
    (spliceFamily_commonLevels hn hd H htop)

/-- The splice fixes the entire old depth prefix. -/
theorem splice_toFun_of_lt [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (s : Node ι) (hs : s.length < d) :
    (splice hn hd H htop).toFun s = s :=
  BoundaryGraft.graft_toFun_of_lt
    (spliceFamily hn hd H htop)
    (spliceFamily_commonLevels hn hd H htop) s hs

/-- If a used frontier lies below a source node `z`, applying the splice to
`z` lands in the range of `H`. -/
theorem splice_image_mem_range_of_frontier_prefix
    [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1)
    (r : LevelNode ι n) (z : Node ι)
    (hpref : (frontierNode hn hd H htop r).1.IsPrefix z) :
    (splice hn hd H htop).toFun z ∈ StrongEmbedding.range H := by
  let p : LevelNode ι d := frontierNode hn hd H htop r
  have hpExists :
      ∃ r' : LevelNode ι n, frontierNode hn hd H htop r' = p :=
    ⟨r, rfl⟩
  have hzge : d ≤ z.length := by
    have := hpref.length_le
    simpa [p, (frontierNode hn hd H htop r).2] using this
  change
    BoundaryGraft.graftFun (spliceFamily hn hd H htop) z ∈
      StrongEmbedding.range H
  rw [BoundaryGraft.graftFun_of_ge
    (spliceFamily hn hd H htop) z hzge]
  have hbp :
      BoundaryGraft.boundaryPrefix d z hzge = p := by
    apply Subtype.ext
    dsimp [BoundaryGraft.boundaryPrefix, p]
    have htake :
        z.take d = (frontierNode hn hd H htop r).1 := by
      have h := List.prefix_iff_eq_take.mp hpref
      rw [(frontierNode hn hd H htop r).2] at h
      exact h.symm
    exact htake
  rw [hbp]
  have hreconstruct :=
    spliceFamily_reconstruct hn hd H htop p hpExists (z.drop d)
  exact ⟨(assignedSource hn hd H htop p).1 ++ z.drop d,
    hreconstruct.symm⟩


/-- Composing the splice under an ambient tree preserves the depth-`d`
approximation. -/
theorem approx_comp_splice [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (B H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1) :
    StrongTreeSpace.approx ι d
        (StrongEmbedding.comp B (splice hn hd H htop)) =
      StrongTreeSpace.approx ι d B := by
  dsimp [splice]
  exact BoundaryGraft.approx_comp_graft B
    (spliceFamily hn hd H htop)
    (spliceFamily_commonLevels hn hd H htop)

/-- The ambient composition with the splice lies in `[d,B]`. -/
theorem comp_splice_mem_levelNeighborhood [Nonempty ι] {n d : ℕ}
    (hn : 0 < n) (hd : 0 < d)
    (B H : StrongEmbedding ι)
    (htop :
      ∀ q : LevelNode ι (n - 1),
        (H.toFun q.1).length = d - 1) :
    StrongEmbedding.comp B (splice hn hd H htop) ∈
      (StrongTreeSpace.approximationSystem ι).levelNeighborhood d B := by
  constructor
  · exact ⟨splice hn hd H htop, rfl⟩
  · exact approx_comp_splice hn hd B H htop

end AmalgamationBoundary
end Milliken
