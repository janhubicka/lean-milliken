import Milliken.GeneralTree.HeterogeneousCommonIndex
import Milliken.GeneralTree.BoundaryGraftStrong
import Milliken.GeneralTree.SubsequenceStrong

/-!
# A synchronized marked-boundary graft in a heterogeneous tree family

Fix synchronized strong trees P_i and one selected node base_i on
source level n in each coordinate. Suppose R_i strongly refines the
cone of P_i rooted at base_i and all R_i share a common ambient
level map M.

The common-source-index theorem supplies a *single* strictly
increasing index subsequence f, valid in every marked cone.
Keep R_i in the marked cone and use a canonical f-subsequence
strong subtree in every other source-n cone. Grafting all the
chosen cone refinements produces synchronized refinements S_i
of P_i, with their first n source levels unchanged.

Crucially every node of S_i above base_i lies in R_i, so a
property established by a local Halpern--Läuchli refinement
of the marked cone survives the global graft. This is the
geometric local-stabilization step for heterogeneous HDHL.

No global branching-degree bound and no Ramsey premise occur.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ}

/-- Graft a synchronized family of marked cone refinements into
every factor, filling all other genuine boundary cones with
a common source-index subsequence. -/
theorem exists_synchronizedMarkedBoundaryGraft
    (P : Fin d → StrongSubtree U)
    (hd : 0 < d)
    (n : ℕ)
    (base : HeterogeneousLevelTuple P n)
    (L M : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (R : Fin d → StrongSubtree U)
    (hR : ∀ i, (R i).levels = M)
    (hRB : ∀ i, (R i).Refines
      (heterogeneousBoundaryCones P n base i)) :
    ∃ S : Fin d → StrongSubtree U,
      (∀ i, (S i).Refines (P i) ∧
        (S i).levels = (P i).boundaryGraftLevels n M ∧
        r n (S i) = r n (P i)) ∧
      (∀ i (z : U), z ∈ (S i).carrier →
        base.1 i ≤ z → z ∈ (R i).carrier) ∧
      (∀ i, (R i).root ∈ (S i).sourceLevel n) := by
  classical
  obtain ⟨f, hf, hMf, _⟩ :=
    exists_heterogeneousBoundary_commonIndex
      P hd n base L M hP R hR hRB
  have hMmono : StrictMono M := by
    let i0 : Fin d := ⟨0, hd⟩
    rw [← hR i0]
    exact (R i0).levels_strictMono
  let mark : (i : Fin d) → SourceBoundary (P i) n :=
    fun i => ⟨base.1 i, base.2 i⟩
  let G : (i : Fin d) → SourceBoundary (P i) n →
      StrongSubtree U :=
    fun i j =>
      if j = mark i then R i else
        (boundaryCones (P i) n j).subsequenceStrong f hf
  have hGref :
      ∀ i j, (G i j).Refines
        (boundaryCones (P i) n j) := by
    intro i j
    by_cases heq : j = mark i
    · subst j
      simpa only [G, ite_true, mark, heterogeneousBoundaryCones]
        using hRB i
    · simpa only [G, heq, ite_false] using
        (boundaryCones (P i) n j).subsequenceStrong_refines f hf
  have hGlev : ∀ i j, (G i j).levels = M := by
    intro i j
    by_cases heq : j = mark i
    · subst j
      simpa only [G, ite_true] using hR i
    · have hlev :=
        (boundaryCones (P i) n j).subsequenceStrong_levels f hf
      have heval : ∀ k,
          (boundaryCones (P i) n j).levels (f k) = M k := by
        intro k
        calc
          (boundaryCones (P i) n j).levels (f k) =
              (P i).levels (n + f k) := rfl
          _ = L (n + f k) := congrFun (hP i) (n + f k)
          _ = M k := (hMf k).symm
      have hfinal : ((boundaryCones (P i) n j).subsequenceStrong f hf).levels = M := by
        rw [hlev]
        funext k
        exact heval k
      simpa only [G, heq, ite_false] using hfinal
  let S : Fin d → StrongSubtree U :=
    fun i => (P i).boundaryGraftStrong n (G i) M
      (hGref i) (hGlev i) hMmono
  refine ⟨S, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · exact (P i).boundaryGraftStrong_refines n
        (G i) M (hGref i) (hGlev i) hMmono
    · exact (P i).boundaryGraftStrong_levels n
        (G i) M (hGref i) (hGlev i) hMmono
    · exact (P i).boundaryGraftStrong_approx n
        (G i) M (hGref i) (hGlev i) hMmono
  · intro i z hz hbasez
    have hzG : z ∈ (P i).boundaryGraftCarrier n (G i) := by
      change z ∈ ((P i).boundaryGraftStrong n (G i)
        M (hGref i) (hGlev i) hMmono).carrier at hz
      rw [(P i).boundaryGraftStrong_carrier n
        (G i) M (hGref i) (hGlev i) hMmono] at hz
      exact hz
    rcases hzG with hstem | htail
    · have hlt : U.level z < (P i).levels n :=
        (P i).initialPart_level_lt n hstem
      have hge : (P i).levels n ≤ U.level z := by
        calc
          (P i).levels n = U.level (base.1 i) := (base.2 i).2.symm
          _ ≤ U.level z := U.level_mono hbasez
      omega
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp htail
      have hzCone : z ∈ (boundaryCones (P i) n j).carrier :=
        hGref i j hj
      have hjz : j.1 ≤ z := hzCone.2
      have hlevels : U.level j.1 = U.level (base.1 i) :=
        j.2.2.trans (base.2 i).2.symm
      have hmatch : j.1 = base.1 i :=
        U.eq_of_common_descendant_of_level_eq
          hjz hbasez hlevels
      have heq : j = mark i := Subtype.ext hmatch
      subst j
      simpa only [G, ite_true] using hj
  · intro i
    have hsource :=
      (P i).boundaryGraftStrong_sourceLevel_at
        n (G i) M (hGref i) (hGlev i) hMmono
    change (R i).root ∈
      ((P i).boundaryGraftStrong n (G i)
        M (hGref i) (hGlev i) hMmono).sourceLevel n
    rw [hsource]
    refine ⟨mark i, ?_⟩
    dsimp [G]
    simp

end GeneralTree
end Milliken
