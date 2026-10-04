import Milliken.Cone

/-!
# Rebasing a strong embedding after a fixed target prefix

If a fixed word `p` is a prefix of the root image of a strong embedding
`E`, then it is a prefix of every image of `E`.  Removing that common
prefix therefore gives another strong embedding.

This is the source-tree operation needed for A.3(2): after choosing a
boundary node of the ambient tree, a cone of a smaller strong subtree can be
viewed as a strong subtree inside that boundary cone.
-/

namespace Milliken
namespace StrongEmbedding

universe u

variable {ι : Type u}

/-- A prefix of the root image is a prefix of every image. -/
theorem rootPrefix_all (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun [])) (s : Node ι) :
    p.IsPrefix (E.toFun s) :=
  hp.trans (E.prefix_mono (List.nil_prefix))

/-- Remove a fixed common target prefix. -/
def rebaseFun (E : StrongEmbedding ι) (p : Node ι)
    (s : Node ι) : Node ι :=
  (E.toFun s).drop p.length

/-- Reattaching the common prefix recovers the original image. -/
theorem rebaseFun_reconstruct
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun [])) (s : Node ι) :
    p ++ rebaseFun E p s = E.toFun s := by
  have hps := rootPrefix_all E hp s
  have htake : (E.toFun s).take p.length = p :=
    (List.prefix_iff_eq_take.mp hps).symm
  calc
    p ++ rebaseFun E p s
        = (E.toFun s).take p.length ++ (E.toFun s).drop p.length := by
            rw [htake]
    _ = E.toFun s := List.take_append_drop _ _

theorem rebaseFun_injective
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun [])) :
    Function.Injective (rebaseFun E p) := by
  intro s t hst
  apply E.injective
  rw [← rebaseFun_reconstruct E hp s,
      ← rebaseFun_reconstruct E hp t, hst]

theorem rebaseFun_prefix_mono
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun []))
    {s t : Node ι} (hst : s.IsPrefix t) :
    (rebaseFun E p s).IsPrefix (rebaseFun E p t) := by
  exact (E.prefix_mono hst).drop p.length

theorem rebaseFun_prefix_reflect
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun []))
    {s t : Node ι}
    (hst : (rebaseFun E p s).IsPrefix (rebaseFun E p t)) :
    s.IsPrefix t := by
  apply E.prefix_reflect
  rw [← rebaseFun_reconstruct E hp s,
      ← rebaseFun_reconstruct E hp t]
  exact prefix_append_left p hst

theorem rebaseFun_branch
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun []))
    (s : Node ι) (i : ι) :
    (child (rebaseFun E p s) i).IsPrefix
      (rebaseFun E p (child s i)) := by
  have h := E.branch s i
  rw [← rebaseFun_reconstruct E hp s,
      ← rebaseFun_reconstruct E hp (child s i)] at h
  have h' :
      (p ++ child (rebaseFun E p s) i).IsPrefix
        (p ++ rebaseFun E p (child s i)) := by
    simpa [child, List.append_assoc] using h
  exact prefix_cancel_left p h'

theorem rebaseFun_branch_reflect
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun []))
    (s t : Node ι) (i : ι)
    (h :
      (child (rebaseFun E p s) i).IsPrefix
        (rebaseFun E p t)) :
    (child s i).IsPrefix t := by
  apply E.branch_reflect s t i
  rw [← rebaseFun_reconstruct E hp s,
      ← rebaseFun_reconstruct E hp t]
  have h' :
      (p ++ child (rebaseFun E p s) i).IsPrefix
        (p ++ rebaseFun E p t) :=
    prefix_append_left p h
  simpa [child, List.append_assoc] using h'

/-- Rebase a strong embedding after a fixed prefix of its root image. -/
def rebase (E : StrongEmbedding ι) (p : Node ι)
    (hp : p.IsPrefix (E.toFun [])) :
    StrongEmbedding ι where
  toFun := rebaseFun E p
  injective := rebaseFun_injective E hp
  prefix_mono := rebaseFun_prefix_mono E hp
  prefix_reflect := rebaseFun_prefix_reflect E hp
  branch := rebaseFun_branch E hp
  branch_reflect := rebaseFun_branch_reflect E hp
  level_witness := by
    rcases E.level_witness with ⟨levels, hmono, hlevels⟩
    have hp0 : p.length ≤ levels 0 := by
      have hlen := hp.length_le
      simpa [hlevels []] using hlen
    refine ⟨fun n => levels n - p.length, ?_, ?_⟩
    · intro a b hab
      have hpa : p.length ≤ levels a :=
        hp0.trans (hmono.monotone (Nat.zero_le a))
      have hlt := hmono hab
      omega
    · intro s
      simp [rebaseFun, List.length_drop, hlevels]

@[simp] theorem rebase_toFun
    (E : StrongEmbedding ι) (p : Node ι)
    (hp : p.IsPrefix (E.toFun [])) (s : Node ι) :
    (rebase E p hp).toFun s = (E.toFun s).drop p.length :=
  rfl

theorem prefix_append_rebase
    (E : StrongEmbedding ι) {p : Node ι}
    (hp : p.IsPrefix (E.toFun [])) (s : Node ι) :
    p ++ (rebase E p hp).toFun s = E.toFun s :=
  rebaseFun_reconstruct E hp s

end StrongEmbedding
end Milliken
