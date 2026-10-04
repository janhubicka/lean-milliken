import Milliken.GraftRamsey
import Milliken.HalpernLauchli.Statement
import Mathlib.Data.Set.Finite.List

/-!
# Chapter 6: Halpern--Läuchli on the boundary of a finite strong stem

This file begins the direct formalization of Todorčević, Lemma 6.1.
The first step is purely an indexing change: the strong-subtree
Halpern--Läuchli theorem is stated for a finite product indexed by `Fin d`,
whereas the one-step extension of an `n`-level strong tree has one
coordinate for each source node on level `n`.

Since that level is finite, the two forms are equivalent.  We expose the
boundary-indexed form so the rest of the Chapter 6 proof can follow the book
without carrying an arbitrary enumeration through every statement.
-/

namespace Milliken
namespace Chapter6

universe u

variable {ι : Type u}

/-- A level of the homogeneous finitely-branching tree is finite. -/
theorem finite_levelNode [Finite ι] (n : ℕ) :
    Finite (LevelNode ι n) :=
  (List.finite_length_eq ι n).to_subtype

/-- Halpern--Läuchli indexed directly by the boundary nodes of a finite
strong stem. -/
def BoundaryHL (ι : Type u) [Finite ι] [Nonempty ι] : Prop :=
  ∀ (n colors : ℕ) [NeZero colors]
      (c : (LevelNode ι n → Node ι) → Fin colors),
    ∃ color : Fin colors,
      ∃ F : LevelNode ι n → StrongEmbedding ι,
        BoundaryGraft.HasCommonLevels F ∧
          ∀ (m : ℕ) (x : LevelNode ι n → Node ι),
            (∀ q, (x q).length = m) →
              c (fun q => (F q).toFun (x q)) = color

/-- The standard `Fin d` formulation of strong-subtree Halpern--Läuchli
implies the boundary-indexed form needed in Lemma 6.1. -/
theorem boundaryHL_of_strongSubtreeHL
    [Finite ι] [Nonempty ι]
    (hHL : HalpernLauchli.StrongSubtreeHL ι) :
    BoundaryHL ι := by
  intro n colors hcolors c
  letI : Finite (LevelNode ι n) := finite_levelNode n
  letI : Fintype (LevelNode ι n) := Fintype.ofFinite _
  let d := Fintype.card (LevelNode ι n)
  let e : Fin d ≃ LevelNode ι n :=
    (Fintype.equivFin (LevelNode ι n)).symm
  let c' : (Fin d → Node ι) → Fin colors :=
    fun x => c (fun q => x (e.symm q))
  rcases hHL d colors c' with
    ⟨color, levels, G, hGlevels, hhom⟩
  let F : LevelNode ι n → StrongEmbedding ι :=
    fun q => G (e.symm q)
  refine ⟨color, F, ?_, ?_⟩
  · refine ⟨levels, hGlevels.1, ?_⟩
    intro q s
    exact hGlevels.2 (e.symm q) s
  · intro m x hx
    have hh :=
      hhom m (fun i => x (e i)) (by
        intro i
        exact hx (e i))
    change c (fun q => (F q).toFun (x q)) = color
    simpa [c', F] using hh


/-- A family of cones rooted at a boundary tuple. -/
def tupleCones {n : ℕ}
    (x : LevelNode ι n → Node ι) :
    LevelNode ι n → StrongEmbedding ι :=
  fun q => StrongEmbedding.cone StrongEmbedding.id (x q)

/-- If the roots of the boundary cones lie on one level, the cone family
has common level sets. -/
theorem tupleCones_commonLevels {n m : ℕ}
    (x : LevelNode ι n → Node ι)
    (hx : ∀ q, (x q).length = m) :
    BoundaryGraft.HasCommonLevels (tupleCones x) := by
  refine ⟨fun k => m + k, ?_, ?_⟩
  · intro a b hab
    omega
  · intro q s
    simp [tupleCones, List.length_append, hx q]

/-- The boundary graft determined by one common-level tuple.  It fixes all
source nodes below level `n` and sends a boundary node `q` into the cone
rooted at `x q`. -/
noncomputable def tupleGraft {n m : ℕ}
    (x : LevelNode ι n → Node ι)
    (hx : ∀ q, (x q).length = m) [Nonempty ι] :
    StrongEmbedding ι :=
  BoundaryGraft.graft (tupleCones x)
    (tupleCones_commonLevels x hx)

/-- The `(n+1)`st finite approximation obtained from a boundary tuple
inside an ambient strong tree. -/
noncomputable def tupleApprox {n m : ℕ}
    (T : StrongEmbedding ι)
    (x : LevelNode ι n → Node ι)
    (hx : ∀ q, (x q).length = m) [Nonempty ι] :
    StrongTreeSpace.Approx ι (n + 1) :=
  StrongTreeSpace.approx ι (n + 1)
    (StrongEmbedding.comp T (tupleGraft x hx))

/-- Every common-level boundary tuple determines a genuine one-step
extension of the canonical stem `r_n(T)` inside `T`. -/
theorem tupleApprox_mem_oneStep
    [Nonempty ι] {n m : ℕ}
    (T : StrongEmbedding ι)
    (x : LevelNode ι n → Node ι)
    (hx : ∀ q, (x q).length = m) :
    tupleApprox T x hx ∈
      (StrongTreeSpace.approximationSystem ι).oneStepApproximations
        (StrongTreeSpace.approx ι n T) T := by
  let X : StrongEmbedding ι :=
    StrongEmbedding.comp T (tupleGraft x hx)
  refine ⟨X, ?_, rfl⟩
  constructor
  · exact BoundaryGraft.comp_graft_le T (tupleCones x)
      (tupleCones_commonLevels x hx)
  · exact BoundaryGraft.approx_comp_graft T (tupleCones x)
      (tupleCones_commonLevels x hx)

/-- Boundary tuples which happen to lie on a common level. -/
def IsBoundaryLevelVector {n : ℕ}
    (x : LevelNode ι n → Node ι) : Prop :=
  ∃ m, ∀ q, (x q).length = m

/-- Binary coloring of boundary tuples induced by a coloring of one-step
finite approximations.  Non-level tuples receive the default color zero;
Halpern--Läuchli only tests the coloring on common-level tuples. -/
noncomputable def boundaryColor [Nonempty ι] {n : ℕ}
    (T : StrongEmbedding ι)
    (O : Set (StrongTreeSpace.Approx ι (n + 1)))
    (x : LevelNode ι n → Node ι) : Fin 2 :=
  if h : IsBoundaryLevelVector x then
    let m := Classical.choose h
    let hx : ∀ q, (x q).length = m :=
      Classical.choose_spec h
    if tupleApprox T x hx ∈ O then 0 else 1
  else 0

/-- On a common-level tuple, color zero is exactly membership of the
corresponding one-step approximation in `O`. -/
theorem boundaryColor_eq_zero_iff [Nonempty ι] {n m : ℕ}
    (T : StrongEmbedding ι)
    (O : Set (StrongTreeSpace.Approx ι (n + 1)))
    (x : LevelNode ι n → Node ι)
    (hx : ∀ q, (x q).length = m) :
    boundaryColor T O x = 0 ↔
      tupleApprox T x hx ∈ O := by
  classical
  unfold boundaryColor
  have hlevel : IsBoundaryLevelVector x := ⟨m, hx⟩
  simp only [dif_pos hlevel]
  let m' := Classical.choose hlevel
  let hx' : ∀ q, (x q).length = m' :=
    Classical.choose_spec hlevel
  have happrox :
      tupleApprox T x hx' = tupleApprox T x hx := by
    apply Subtype.ext
    funext s
    rfl
  by_cases hO : tupleApprox T x hx ∈ O
  · have hO' : tupleApprox T x hx' ∈ O := by
      simpa [happrox] using hO
    simp [m', hx', hO', hO]
  · have hO' : tupleApprox T x hx' ∉ O := by
      simpa [happrox] using hO
    simp [m', hx', hO', hO]

end Chapter6
end Milliken
