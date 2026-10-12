import Milliken.GeneralTree.CodePoint

/-!
# Protected fusion limits for arbitrary locally finite strong trees

A descending sequence S₀ ⊇ S₁ ⊇ ... of genuine strong subtrees,
with r_(n+1)(S_(n+1)) = r_(n+1)(S_n), determines an infinite
strong-tree limit. We construct the limit *without A.4* by
forming its full sequence of finite approximations and using
the already proved reconstruction of a prefix-realizable
general-tree code.

The limit has exactly the protected finite source approximations:
r_n(X) = r_n(S_n), and therefore its nth selected source level
equals the nth source level of S_(n+1). Moreover X refines every
stage. None of these statements assumes a Ramsey theorem,
bounded branching, or homogeneous alphabets.

This is the general-tree counterpart of the fusion-completeness
lemma used in Todorčević's homogeneous stabilization proof.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree}

/-- In a protected sequence all prior approximations stay fixed
at every later stage. -/
theorem generalFusionApprox_stable
    (S : ℕ → StrongSubtree U)
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n))
    {n k : ℕ} (hnk : n ≤ k) :
    r n (S k) = r n (S n) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      rfl
  | succ k hnk ih =>
      have hstep : r n (S (k + 1)) = r n (S k) :=
        r_coherent_le (S (k + 1)) (S k)
          (k + 1) (happrox k) n (by omega)
      exact hstep.trans ih

/-- Adjacent inclusion implies inclusion through the entire
descending sequence. -/
theorem generalFusionSequence_refines
    (S : ℕ → StrongSubtree U)
    (hstep : ∀ n, (S (n + 1)).Refines (S n))
    {n k : ℕ} (hnk : n ≤ k) :
    (S k).Refines (S n) := by
  induction k, hnk using Nat.le_induction with
  | base =>
      exact StrongSubtree.refines_refl (S n)
  | succ k hnk ih =>
      exact StrongSubtree.refines_trans (hstep k) ih

/-- Code consisting of the nth protected approximation of stage n. -/
def generalFusionCode
    (S : ℕ → StrongSubtree U) : GeneralCode U :=
  fun n => r n (S n)

/-- Every prefix of the protected fusion code is realized by
the corresponding finite-stage strong subtree. -/
theorem generalFusionCode_prefixRealizable
    (S : ℕ → StrongSubtree U)
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n)) :
    ∀ N : ℕ, CodePrefixRealizable (generalFusionCode S) N := by
  intro N
  refine ⟨S N, ?_⟩
  intro n hn
  exact generalFusionApprox_stable S happrox hn

/-- The genuine infinite strong-tree limit, reconstructed
non-circularly from the coherent protected finite approximations. -/
noncomputable def generalFusionLimit
    (S : ℕ → StrongSubtree U)
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n)) :
    StrongSubtree U :=
  pointOfGeneralCode (generalFusionCode S)
    (generalFusionCode_prefixRealizable S happrox)

/-- Each finite approximation of the limit is exactly the
corresponding approximation of the sequence. -/
theorem generalFusionLimit_approx
    (S : ℕ → StrongSubtree U)
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n))
    (n : ℕ) :
    r n (generalFusionLimit S happrox) = r n (S n) :=
  pointOfGeneralCode_approx (generalFusionCode S)
    (generalFusionCode_prefixRealizable S happrox) n

/-- Each selected source level of the fusion limit is exactly
the protected level in the next stage. -/
theorem generalFusionLimit_sourceLevel
    (S : ℕ → StrongSubtree U)
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n))
    (n : ℕ) :
    (generalFusionLimit S happrox).sourceLevel n =
      (S (n + 1)).sourceLevel n := by
  calc
    (generalFusionLimit S happrox).sourceLevel n =
        maxLevel (r (n + 1) (generalFusionLimit S happrox)) :=
      (maxLevel_r_succ (generalFusionLimit S happrox) n).symm
    _ = maxLevel (r (n + 1) (S (n + 1))) := by
      rw [generalFusionLimit_approx]
    _ = (S (n + 1)).sourceLevel n :=
      maxLevel_r_succ (S (n + 1)) n

/-- The reconstructed limit is contained in every stage of the
descending sequence, not just in the first one. -/
theorem generalFusionLimit_refines
    (S : ℕ → StrongSubtree U)
    (hstep : ∀ n, (S (n + 1)).Refines (S n))
    (happrox : ∀ n,
      r (n + 1) (S (n + 1)) = r (n + 1) (S n))
    (k : ℕ) :
    (generalFusionLimit S happrox).Refines (S k) := by
  intro z hz
  change z ∈ codeCarrier (generalFusionCode S) at hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  by_cases hk : k ≤ n + 1
  · have hfront : z ∈ (S (n + 1)).sourceLevel n := by
      rw [← codeFrontier_eq_sourceLevel
        (generalFusionCode S) (S (n + 1)) n rfl]
      exact hn
    exact (generalFusionSequence_refines S hstep hk) hfront.1
  · have hnk : n + 1 ≤ k := by omega
    have heq :
        r (n + 1) (S k) = (generalFusionCode S) (n + 1) :=
      generalFusionApprox_stable S happrox hnk
    have hfront : z ∈ (S k).sourceLevel n := by
      rw [← codeFrontier_eq_sourceLevel
        (generalFusionCode S) (S k) n heq]
      exact hn
    exact hfront.1

end GeneralTree
end Milliken
