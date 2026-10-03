import Milliken.HalpernLauchli.Density

/-!
# The base of Todorčević's Halpern--Läuchli induction

Section 3.2 proves the highly-dense-set form `HDHL_d` by induction on the
number of tree factors.  The one-dimensional case is immediate in the book;
we spell it out here because the resulting projection construction is reused
when passing between dense subsets of a product and actual matrices.
-/

namespace Milliken
namespace HalpernLauchli

universe u

variable {ι : Type u}

/-- Turn a set of unary level-vectors into its coordinate projection. -/
def unaryProjection (P : Set (Fin 1 → Node ι)) : Matrix ι 1 where
  coord := fun _ => {t | ∃ x ∈ P, x 0 = t}

theorem unaryProjection_carrier_subset
    (P : Set (Fin 1 → Node ι)) :
    (unaryProjection P).carrier ⊆ P := by
  intro x hx
  have hx0 := hx (0 : Fin 1)
  rcases hx0 with ⟨y, hyP, hy0⟩
  have hxy : x = y := by
    funext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst i
    exact hy0.symm
  simpa [hxy] using hyP

theorem unaryProjection_dense
    {P : Set (Fin 1 → Node ι)} {k : ℕ}
    (hP : ProductDenseAt P k) :
    (unaryProjection P).DenseAt k := by
  intro i s hs
  let x : Fin 1 → Node ι := fun _ => s
  have hx : IsLevelVectorAt k x := by
    intro j
    simpa [x, treeLevel] using hs
  rcases hP x hx with ⟨y, hyP, hxy⟩
  refine ⟨y 0, ?_, hxy 0⟩
  exact ⟨y, hyP, rfl⟩

theorem unaryProjection_onLevel
    {P : Set (Fin 1 → Node ι)} {l : ℕ}
    (hP : ∀ x ∈ P, IsLevelVectorAt l x) :
    (unaryProjection P).OnLevel l := by
  intro i t ht
  rcases ht with ⟨x, hxP, hxt⟩
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst i
  rw [← hxt]
  exact hP x hxP 0

/-- The strengthened, level-matrix base case of the induction. -/
theorem levelHDHL_one (ι : Type u) :
    LevelHDHL ι 1 := by
  intro P hP k hk
  rcases hP k with ⟨n, hn⟩
  let M : Matrix ι 1 := Matrix.fullLevel n
  have hM : M.DenseAt n := by
    dsimp [M]
    exact Matrix.fullLevel_dense (ι := ι) (d := 1) n
  have hQ : ProductDenseAt (P ∩ M.carrier) k :=
    hn M hM
  let N : Matrix ι 1 := unaryProjection (P ∩ M.carrier)
  have hNlevel : N.OnLevel n := by
    dsimp [N]
    apply unaryProjection_onLevel
    intro x hx i
    exact hx.2 i
  refine ⟨N, ?_, ?_⟩
  · refine ⟨n, hNlevel, ?_⟩
    dsimp [N]
    exact unaryProjection_dense hQ
  · dsimp [N]
    exact (unaryProjection_carrier_subset (P ∩ M.carrier)).trans
      Set.inter_subset_left

/-- The base case `HDHL₁` of the induction in Section 3.2. -/
theorem hdhl_one (ι : Type u) :
    HDHL ι 1 :=
  hdhl_of_levelHDHL (levelHDHL_one ι)

end HalpernLauchli
end Milliken
