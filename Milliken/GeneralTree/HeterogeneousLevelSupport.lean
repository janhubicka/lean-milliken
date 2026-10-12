import Milliken.GeneralTree.HeterogeneousDensity

/-!
# Source-rank support and finite-level matrix geometry for arbitrary trees

Todorčević's Lemma 3.16 and its stabilization induction require
coordinate matrices supported on one level, as well as a
source-height inequality: a matrix supported on selected level
l and dense at selected level n must satisfy n ≤ l
when the dimension is positive.

These facts use only strictly increasing selected levels,
finite/nonempty source levels, and their coordinatewise product.
No fixed branching alphabet or globally bounded degree is assumed.
-/

namespace Milliken
namespace GeneralTree

variable {U : AmbientTree} {d : ℕ} {P : Fin d → StrongSubtree U}

namespace HeterogeneousMatrix

/-- Every coordinate set of an n-dense heterogeneous matrix
is nonempty, because every selected source level of a
strong input tree is nonempty. -/
theorem coord_nonempty_of_denseAt
    (M : HeterogeneousMatrix P) {n : ℕ}
    (hM : M.DenseAt n) :
    ∀ i, (M.coord i).Nonempty := by
  intro i
  obtain ⟨x, hx⟩ := (P i).sourceLevel_nonempty n
  obtain ⟨y, hy, _⟩ := hM i x hx
  exact ⟨y, hy⟩

/-- Coordinatewise n-density implies n-density of the full Cartesian
product matrix carrier. -/
theorem productDenseAt_carrier
    (M : HeterogeneousMatrix P) {n : ℕ}
    (hM : M.DenseAt n) :
    HeterogeneousProductDenseAt P M.carrier n := by
  classical
  intro x
  let y : Fin d → U :=
    fun i => Classical.choose (hM i (x.1 i) (x.2 i))
  have hy (i : Fin d) :
      y i ∈ M.coord i ∧ x.1 i ≤ y i :=
    Classical.choose_spec (hM i (x.1 i) (x.2 i))
  exact ⟨y, (fun i => (hy i).1), (fun i => (hy i).2)⟩

/-- If a matrix is dense at n, while all its nodes
belong to selected level l, then n ≤ l provided
at least one coordinate exists. -/
theorem support_ge_of_onLevel_denseAt
    (M : HeterogeneousMatrix P) {n l : ℕ}
    (hd : 0 < d)
    (hon : M.OnLevel l) (hdense : M.DenseAt n) :
    n ≤ l := by
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨x, hx⟩ := (P i).sourceLevel_nonempty n
  obtain ⟨y, hy, hxy⟩ := hdense i x hx
  have hlevel : (P i).levels n ≤ (P i).levels l := by
    calc
      (P i).levels n = U.level x := hx.2.symm
      _ ≤ U.level y := U.level_mono hxy
      _ = (P i).levels l := (hon i y hy).2
  by_contra hbad
  have hln : l < n := Nat.lt_of_not_ge hbad
  have hstrict := (P i).levels_strictMono hln
  omega

/-- If a matrix's carrier lies in a level-supported matrix and all
its coordinates are nonempty, then each coordinate lies on that level.
The source-level is the actual input-tree level, not an ambient
fixed-alphabet word length. -/
theorem onLevel_of_carrier_subset_of_coord_nonempty
    (A B : HeterogeneousMatrix P) {l : ℕ}
    (hsub : A.carrier ⊆ B.carrier)
    (hB : B.OnLevel l)
    (hne : ∀ i, (A.coord i).Nonempty) :
    A.OnLevel l := by
  classical
  intro i z hz
  choose w hw using hne
  let x : Fin d → U := Function.update w i z
  have hxA : x ∈ A.carrier := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa [x] using hz
    · simpa [x, hji] using hw j
  have hxB : x ∈ B.carrier := hsub hxA
  have hxLevel := hB i (x i) (hxB i)
  simpa [x] using hxLevel

/-- A matrix can be supported on some selected source level
while being dense at a possibly earlier level. -/
def LevelDenseAt (M : HeterogeneousMatrix P) (n : ℕ) : Prop :=
  ∃ l : ℕ, M.OnLevel l ∧ M.DenseAt n

/-- Level-supported density implies ordinary density. -/
theorem denseAt_of_levelDenseAt
    (M : HeterogeneousMatrix P) {n : ℕ}
    (hM : M.LevelDenseAt n) : M.DenseAt n :=
  hM.choose_spec.2

end HeterogeneousMatrix
end GeneralTree
end Milliken
