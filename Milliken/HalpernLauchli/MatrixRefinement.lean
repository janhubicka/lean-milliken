import Milliken.HalpernLauchli.Sections
import Milliken.HalpernLauchli.Asymmetric

/-!
# Refining later dense matrices over earlier level matrices

In Todorčević's proof of Lemma 3.15, equation (3) tacitly shrinks a later
`x-n`-dense matrix so that it lies above an earlier level matrix.  This
file makes that operation explicit.

For matrices `A` and `B`, `A.refineOver B` keeps exactly those points
of `B` which extend some point of `A`, coordinate by coordinate.  If
`B` is dense sufficiently far above the supporting level of `A`, this
refinement still inherits the earlier density of `A`.  Under the
stabilization property (*), section-avoidance also propagates from `A`
to the refinement.
-/

namespace Milliken
namespace HalpernLauchli

universe u
variable {ι : Type u}

namespace Matrix

variable {d : ℕ}

/-- Restricting an already cone-dense matrix to the same cone preserves its
cone density. -/
theorem restrictAbove_denseAbove_self
    {M : Matrix ι d} {base : Fin d → Node ι} {n : ℕ}
    (hM : M.DenseAbove base n) :
    (M.restrictAbove base).DenseAbove base n := by
  intro i t ht
  rcases hM i ht with ⟨y, hyM, hty⟩
  refine ⟨y, ?_, hty⟩
  exact ⟨hyM, ht.1.trans hty⟩

/-- The supporting level of a nontrivial cone-dense level matrix is
at least its density scale. -/
theorem support_ge_of_onLevel_denseAbove [Nonempty ι]
    {M : Matrix ι d} {base : Fin d → Node ι}
    {k n l : ℕ} (hd : 0 < d)
    (hbase : IsLevelVectorAt k base)
    (hkn : k ≤ n)
    (hlevel : M.OnLevel l)
    (hdense : M.DenseAbove base n) :
    n ≤ l := by
  let i0 : Fin d := ⟨0, hd⟩
  let u : Node ι := extendToLevel (base i0) n
  have hbaseN : (base i0).length ≤ n := by
    rw [hbase i0]
    exact hkn
  have hprefix : (base i0).IsPrefix u :=
    prefix_extendToLevel _ _
  have hulen : u.length = n :=
    length_extendToLevel hbaseN
  rcases hdense i0
      (show u ∈ coneLevel (base i0) n from
        ⟨hprefix, hulen⟩) with
    ⟨z, hzM, huz⟩
  have hzlen : z.length = l := hlevel i0 z hzM
  have hlen := huz.length_le
  rw [hulen, hzlen] at hlen
  exact hlen

/-- Keep the part of `B` which lies above `A`, coordinatewise. -/
def refineOver (A B : Matrix ι d) : Matrix ι d where
  coord := fun i => {z | z ∈ B.coord i ∧
    ∃ a ∈ A.coord i, a.IsPrefix z}

theorem refineOver_carrier_subset_right (A B : Matrix ι d) :
    (A.refineOver B).carrier ⊆ B.carrier := by
  intro z hz i
  exact (hz i).1

theorem refineOver_onLevel {A B : Matrix ι d} {l : ℕ}
    (hB : B.OnLevel l) :
    (A.refineOver B).OnLevel l := by
  intro i z hz
  exact hB i z hz.1

/-- Every vector in the refined matrix has a coordinatewise predecessor in
the earlier matrix. -/
theorem exists_predecessor_of_mem_refineOver
    {A B : Matrix ι d} {z : Fin d → Node ι}
    (hz : z ∈ (A.refineOver B).carrier) :
    ∃ a ∈ A.carrier, ∀ i, (a i).IsPrefix (z i) := by
  classical
  choose a haA haz using fun i => (hz i).2
  refine ⟨a, ?_, haz⟩
  intro i
  exact haA i

/-- A sufficiently later dense matrix can be shrunk over an earlier level
matrix without losing the earlier density. -/
theorem refineOver_denseAbove [Nonempty ι]
    {A B : Matrix ι d} {base : Fin d → Node ι}
    {k n l : ℕ}
    (hAlevel : A.OnLevel l)
    (hA : A.DenseAbove base k)
    (hB : B.DenseAbove base n)
    (hln : l ≤ n) :
    (A.refineOver B).DenseAbove base k := by
  intro i u hu
  rcases hA i hu with ⟨a, haA, hua⟩
  have halen : a.length = l := hAlevel i a haA
  have haln : a.length ≤ n := by
    rw [halen]
    exact hln
  let v : Node ι := extendToLevel a n
  have hav : a.IsPrefix v := prefix_extendToLevel a n
  have hvlen : v.length = n := length_extendToLevel haln
  have hbasev : (base i).IsPrefix v :=
    hu.1.trans (hua.trans hav)
  rcases hB i
      (show v ∈ coneLevel (base i) n from ⟨hbasev, hvlen⟩) with
    ⟨z, hzB, hvz⟩
  refine ⟨z, ?_, hua.trans (hav.trans hvz)⟩
  exact ⟨hzB, ⟨a, haA, hav.trans hvz⟩⟩

/-- Stabilization (*) propagates avoidance from an earlier level matrix to a
later refinement lying coordinatewise above it. -/
theorem refineOver_avoids_section
    {A B : Matrix ι d} (hd : 0 < d)
    {P : Set (Fin (d + 1) → Node ι)}
    (hstab : Stabilized P)
    {y : Node ι} {lA lB : ℕ}
    (hAlevel : A.OnLevel lA)
    (hBlevel : B.OnLevel lB)
    (hyA : y.length < lA)
    (hAavoid : A.carrier ⊆ (lastSection P y)ᶜ) :
    (A.refineOver B).carrier ⊆ (lastSection P y)ᶜ := by
  classical
  intro z hz hzP
  rcases exists_predecessor_of_mem_refineOver hz with
    ⟨a, haA, haz⟩
  have haLevel : IsLevelVectorAt lA a := by
    intro i
    exact hAlevel i (a i) (haA i)
  have hzB : z ∈ B.carrier :=
    refineOver_carrier_subset_right A B hz
  have hzLevel : IsLevelVectorAt lB z := by
    intro i
    exact hBlevel i (z i) (hzB i)
  let i0 : Fin d := ⟨0, hd⟩
  have hlAB : lA ≤ lB := by
    have hlen := (haz i0).length_le
    rw [haLevel i0, hzLevel i0] at hlen
    exact hlen
  have hyB : y.length < lB := hyA.trans_le hlAB
  let q := y.length + 1
  have hqA : q ≤ lA := by
    dsimp [q]
    omega
  have hqB : q ≤ lB := hqA.trans hlAB
  have htrunc :
      truncateVector q a = truncateVector q z := by
    funext i
    have hp := (haz i).take q
    have hqAi : q ≤ (a i).length := by
      rw [haLevel i]
      exact hqA
    have hqZi : q ≤ (z i).length := by
      rw [hzLevel i]
      exact hqB
    have hpa : (a i).take q = (z i).take q :=
      hp.eq_of_length (by
        rw [List.length_take_of_le hqAi,
            List.length_take_of_le hqZi])
    exact hpa
  have hzTrunc :
      truncateVector q z ∈ lastSection P y :=
    (hstab y lB z hzLevel hyB).mp hzP
  have haTrunc :
      truncateVector q a ∈ lastSection P y := by
    rw [htrunc]
    exact hzTrunc
  have haP : a ∈ lastSection P y :=
    (hstab y lA a haLevel hyA).mpr haTrunc
  exact hAavoid haA haP

end Matrix
end HalpernLauchli
end Milliken
